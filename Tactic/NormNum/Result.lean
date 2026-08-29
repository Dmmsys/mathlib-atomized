/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Int.Cast.Basic
public import Qq.MetaM

public meta import Mathlib.Data.Sigma.Basic -- for the `Inhabited (Sigma β)` instance

/-!
## The `Result` type for `norm_num`

We set up predicates `IsNat`, `IsInt`, and `IsRat`,
stating that an element of a ring is equal to the "normal form" of a natural number, integer,
or rational number coerced into that ring.

We then define `Result e`, which contains a proof that a typed expression `e : Q($α)`
is equal to the coercion of an explicit natural number, integer, or rational number,
or is either `true` or `false`.

-/

@[expose] public section

universe u
variable {α : Type u}

open Lean
open Lean.Meta Qq Lean.Elab Term

namespace Mathlib
namespace Meta.NormNum

variable {u : Level}

/-- A shortcut (non)instance for `AddMonoidWithOne α`
from `Semiring α` to shrink generated proofs. -/
@[instance_reducible]
/--
Definition of `instAddMonoidWithOne'` / `instAddMonoidWithOne'` 的定义

English:
definition instAddMonoidWithOne'
  signature: {α : Type u} [Semiring α]
  body: inferInstance

中文:
定义 instAddMonoidWithOne'
  签名: {α : 类型u} [半环 α]
  定义体: inferInstance
-/
def instAddMonoidWithOne' {α : Type u} [Semiring α] : AddMonoidWithOne α := inferInstance

/-- A shortcut (non)instance for `AddMonoidWithOne α` from `Ring α` to shrink generated proofs. -/
@[instance_reducible]
/--
Definition of `instAddMonoidWithOne` / `instAddMonoidWithOne` 的定义

English:
definition instAddMonoidWithOne
  signature: {α : Type u} [Ring α]
  body: inferInstance

中文:
定义 instAddMonoidWithOne
  签名: {α : 类型u} [环 α]
  定义体: inferInstance
-/
def instAddMonoidWithOne {α : Type u} [Ring α] : AddMonoidWithOne α := inferInstance

/--
lemma `instAtLeastTwo` / 引理 `instAtLeastTwo`

English:
lemma instAtLeastTwo
  given: (n : Nat)
  statement: Nat.AtLeastTwo (n + 2)
  proof: inferInstance

中文:
引理 instAtLeastTwo
  条件: (n : 自然数)
  结论: 自然数.AtLeastTwo (n + 2)
  证明: inferInstance
-/
lemma instAtLeastTwo (n : Nat) : Nat.AtLeastTwo (n + 2) := inferInstance

/-- Helper function to synthesize a typed `AddMonoidWithOne α` expression. -/
meta def inferAddMonoidWithOne (α : Q(Type u)) : MetaM Q(AddMonoidWithOne $α) :=
return ← synthInstanceQ q(AddMonoidWithOne $α) >
    throwError "not an AddMonoidWithOne"

/-- Helper function to synthesize a typed `Semiring α` expression. -/
meta def inferSemiring (α : Q(Type u)) : MetaM Q(Semiring $α) :=
return ← synthInstanceQ q(Semiring $α) > throwError "not a semiring"

/-- Helper function to synthesize a typed `Ring α` expression. -/
meta def inferRing (α : Q(Type u)) : MetaM Q(Ring $α) :=
return ← synthInstanceQ q(Ring $α) > throwError "not a ring"

/--
Represent an integer as a "raw" typed expression.

This uses `.lit (.natVal n)` internally to represent a natural number,
rather than the preferred `OfNat.ofNat` form.
We use this internally to avoid unnecessary typeclass searches.

This function is the inverse of `Expr.intLit!`.
-/
meta def mkRawIntLit (n : Int) : Q(Int) :=
  let lit : Q(Nat) := mkRawNatLit n.natAbs
  if 0 <= n then q(.ofNat $lit) else q(.negOfNat $lit)

/--
Represent an integer as a "raw" typed expression.

This `.lit (.natVal n)` internally to represent a natural number,
rather than the preferred `OfNat.ofNat` form.
We use this internally to avoid unnecessary typeclass searches.
-/
meta def mkRawRatLit (q : Rat) : Q(Rat) :=
  let nlit : Q(Int) := mkRawIntLit q.num
  let dlit : Q(Nat) := mkRawNatLit q.den
  q(mkRat $nlit $dlit)

/-- Extract the raw natlit representing the absolute value of a raw integer literal
(of the type produced by `Mathlib.Meta.NormNum.mkRawIntLit`) along with an equality proof. -/
meta def rawIntLitNatAbs (n : Q(Int)) : (m : Q(Nat)) × Q(Int.natAbs $n = $m) :=
  if n.isAppOfArity ``Int.ofNat 1 then
    have m : Q(Nat) := n.appArg!
    ⟨m, show Q(Int.natAbs (Int.ofNat $m) = $m) from q(Int.natAbs_natCast $m)⟩
  else if n.isAppOfArity ``Int.negOfNat 1 then
    have m : Q(Nat) := n.appArg!
    ⟨m, show Q(Int.natAbs (Int.negOfNat $m) = $m) from q(Int.natAbs_neg $m)⟩
  else
    panic! "not a raw integer literal"

/--
Constructs an `ofNat` application `a'` with the canonical instance, together with a proof that
the instance is equal to the result of `Nat.cast` on the given `AddMonoidWithOne` instance.

This function is performance-critical, as many higher level tactics have to construct numerals.
So rather than using typeclass search we hardcode the (relatively small) set of solutions
to the typeclass problem.
-/
meta def mkOfNat (α : Q(Type u)) (_sα : Q(AddMonoidWithOne $α)) (lit : Q(Nat)) :
    MetaM ((a' : Q($α)) × Q($lit = $a')) := do
  if α.isConstOf ``Nat then
    let a' : Q(Nat) := q(OfNat.ofNat $lit : Nat)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else if α.isConstOf ``Int then
    let a' : Q(Int) := q(OfNat.ofNat $lit : Int)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else if α.isConstOf ``Rat then
    let a' : Q(Rat) := q(OfNat.ofNat $lit : Rat)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else
    let some n := lit.rawNatLit? | failure
    match n with
    | 0 => pure ⟨q(0 : $α), (q(Nat.cast_zero (R := $α)) : Expr)⟩
    | 1 => pure ⟨q(1 : $α), (q(Nat.cast_one (R := $α)) : Expr)⟩
    | k+2 =>
      let k : Q(Nat) := mkRawNatLit k
      let _x : Q(Nat.AtLeastTwo $lit) :=
        (q(instAtLeastTwo $k) : Expr)
      let a' : Q($α) := q(OfNat.ofNat $lit)
      pure ⟨a', (q(Eq.refl $a') : Expr)⟩

/--
Definition of `IsNat` / `IsNat` 的定义

English:
structure IsNat
  parameters: {α : Type u} [AddMonoidWithOne α] (a : α) (n : Nat)
  axioms and operations (1):
    - out : a = n

中文:
结构 是自然数
  参数: {α : 类型u} [加法带幺幺半群 α] (a : α) (n : 自然数)
  公理与运算 (1 个):
    - out : a = n
-/
structure IsNat {α : Type u} [AddMonoidWithOne α] (a : α) (n : Nat) : Prop where
  /-- The element is equal to the coercion of the natural number. -/
  out : a = n

/--
theorem `IsNat.raw_refl` / 定理 `IsNat.raw_refl`

English:
theorem IsNat.raw_refl
  given: (n : Nat)
  statement: IsNat n n
  proof: ⟨rfl⟩

中文:
定理 是自然数.raw_refl
  条件: (n : 自然数)
  结论: 是自然数 n n
  证明: ⟨rfl⟩
-/
theorem IsNat.raw_refl (n : Nat) : IsNat n n := ⟨rfl⟩

/--
Definition of `_root_.Nat.rawCast` / `_root_.Nat.rawCast` 的定义

English:
definition _root_.Nat.rawCast
  signature: {α : Type u} [AddMonoidWithOne α] (n : Nat)
  body: n

中文:
定义 _root_.自然数.rawCast
  签名: {α : 类型u} [加法带幺幺半群 α] (n : 自然数)
  定义体: n
-/
@[simp] def _root_.Nat.rawCast {α : Type u} [AddMonoidWithOne α] (n : Nat) : α := n

/--
theorem `IsNat.to_eq` / 定理 `IsNat.to_eq`

English:
theorem IsNat.to_eq
  given: {α : Type u} [AddMonoidWithOne α] {n}
  statement: {a a' : α} -> IsNat a n -> n = a' -> a = a'

中文:
定理 是自然数.to_eq
  条件: {α : 类型u} [加法带幺幺半群 α] {n}
  结论: {a a' : α} -> 是自然数 a n -> n = a' -> a = a'
-/
theorem IsNat.to_eq {α : Type u} [AddMonoidWithOne α] {n} : {a a' : α} -> IsNat a n -> n = a' -> a = a'
  | _, _, ⟨rfl⟩, rfl => rfl

/--
theorem `IsNat.to_raw_eq` / 定理 `IsNat.to_raw_eq`

English:
theorem IsNat.to_raw_eq
  given: {a : α} {n : Nat} [AddMonoidWithOne α]
  statement: IsNat (a : α) n -> a = n.rawCast

中文:
定理 是自然数.to_raw_eq
  条件: {a : α} {n : 自然数} [加法带幺幺半群 α]
  结论: 是自然数 (a : α) n -> a = n.rawCast
-/
theorem IsNat.to_raw_eq {a : α} {n : Nat} [AddMonoidWithOne α] : IsNat (a : α) n -> a = n.rawCast
  | ⟨e⟩ => e

/--
theorem `IsNat.of_raw` / 定理 `IsNat.of_raw`

English:
theorem IsNat.of_raw
  given: (α) [AddMonoidWithOne α] (n : Nat)
  statement: IsNat (n.rawCast : α) n
  proof: ⟨rfl⟩

@[elab_as_elim]

中文:
定理 是自然数.of_raw
  条件: (α) [加法带幺幺半群 α] (n : 自然数)
  结论: 是自然数 (n.rawCast : α) n
  证明: ⟨rfl⟩

@[elab_as_elim]
-/
theorem IsNat.of_raw (α) [AddMonoidWithOne α] (n : Nat) : IsNat (n.rawCast : α) n := ⟨rfl⟩

@[elab_as_elim]
/--
theorem `isNat.natElim` / 定理 `isNat.natElim`

English:
theorem isNat.natElim
  given: {p : Nat -> Prop}
  statement: {n : Nat} -> {n' : Nat} -> IsNat n n' -> p n' -> p n

中文:
定理 is自然数.natElim
  条件: {p : 自然数 -> 命题}
  结论: {n : 自然数} -> {n' : 自然数} -> 是自然数 n n' -> p n' -> p n
-/
theorem isNat.natElim {p : Nat -> Prop} : {n : Nat} -> {n' : Nat} -> IsNat n n' -> p n' -> p n
  | _, _, ⟨rfl⟩, h => h

/--
Definition of `IsInt` / `IsInt` 的定义

English:
structure IsInt
  parameters: [Ring α] (a : α) (n : Int)
  axioms and operations (1):
    - out : a = n

中文:
结构 是整数
  参数: [环 α] (a : α) (n : 整数)
  公理与运算 (1 个):
    - out : a = n
-/
structure IsInt [Ring α] (a : α) (n : Int) : Prop where
  /-- The element is equal to the coercion of the integer. -/
  out : a = n

/--
Definition of `_root_.Int.rawCast` / `_root_.Int.rawCast` 的定义

English:
definition _root_.Int.rawCast
  signature: [Ring α] (n : Int)
  body: n

中文:
定义 _root_.整数.rawCast
  签名: [环 α] (n : 整数)
  定义体: n
-/
@[simp] def _root_.Int.rawCast [Ring α] (n : Int) : α := n

/--
theorem `IsInt.to_isNat` / 定理 `IsInt.to_isNat`

English:
theorem IsInt.to_isNat
  given: {α} [Ring α]
  statement: forall {a : α} {n}, IsInt a (.ofNat n) -> IsNat a n

中文:
定理 是整数.to_is自然数
  条件: {α} [环 α]
  结论: 对任意 {a : α} {n}, 是整数 a (.of自然数 n) -> 是自然数 a n
-/
theorem IsInt.to_isNat {α} [Ring α] : forall {a : α} {n}, IsInt a (.ofNat n) -> IsNat a n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

/--
theorem `IsNat.to_isInt` / 定理 `IsNat.to_isInt`

English:
theorem IsNat.to_isInt
  given: {α} [Ring α]
  statement: forall {a : α} {n}, IsNat a n -> IsInt a (.ofNat n)

中文:
定理 是自然数.to_is整数
  条件: {α} [环 α]
  结论: 对任意 {a : α} {n}, 是自然数 a n -> 是整数 a (.of自然数 n)
-/
theorem IsNat.to_isInt {α} [Ring α] : forall {a : α} {n}, IsNat a n -> IsInt a (.ofNat n)
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

/--
theorem `IsInt.to_raw_eq` / 定理 `IsInt.to_raw_eq`

English:
theorem IsInt.to_raw_eq
  given: {a : α} {n : Int} [Ring α]
  statement: IsInt (a : α) n -> a = n.rawCast

中文:
定理 是整数.to_raw_eq
  条件: {a : α} {n : 整数} [环 α]
  结论: 是整数 (a : α) n -> a = n.rawCast
-/
theorem IsInt.to_raw_eq {a : α} {n : Int} [Ring α] : IsInt (a : α) n -> a = n.rawCast
  | ⟨e⟩ => e

/--
theorem `IsInt.of_raw` / 定理 `IsInt.of_raw`

English:
theorem IsInt.of_raw
  given: (α) [Ring α] (n : Int)
  statement: IsInt (n.rawCast : α) n
  proof: ⟨rfl⟩

中文:
定理 是整数.of_raw
  条件: (α) [环 α] (n : 整数)
  结论: 是整数 (n.rawCast : α) n
  证明: ⟨rfl⟩
-/
theorem IsInt.of_raw (α) [Ring α] (n : Int) : IsInt (n.rawCast : α) n := ⟨rfl⟩

/--
theorem `IsInt.neg_to_eq` / 定理 `IsInt.neg_to_eq`

English:
theorem IsInt.neg_to_eq
  given: {α} [Ring α] {n}

中文:
定理 是整数.neg_to_eq
  条件: {α} [环 α] {n}
-/
theorem IsInt.neg_to_eq {α} [Ring α] {n} :
    {a a' : α} -> IsInt a (.negOfNat n) -> n = a' -> a = -a'
  | _, _, ⟨rfl⟩, rfl => by simp [Int.negOfNat_eq, Int.cast_neg]

/--
theorem `IsInt.nonneg_to_eq` / 定理 `IsInt.nonneg_to_eq`

English:
theorem IsInt.nonneg_to_eq
  statement: {α} [Ring α] {n}
  proof: h.to_isNat.to_eq e

中文:
定理 是整数.nonneg_to_eq
  结论: {α} [环 α] {n}
  证明: h.to_isNat.to_eq e

Depends on / 依赖: h.to_isNat.to_eq, to_eq, to_isNat
-/
theorem IsInt.nonneg_to_eq {α} [Ring α] {n}
    {a a' : α} (h : IsInt a (.ofNat n)) (e : n = a') : a = a' := h.to_isNat.to_eq e

/--
Inductive type `IsRat` / 归纳类型 `IsRat`

English:
inductive IsRat
  parameters: [Ring α] (a : α) (num : Int) (denom : Nat)
  constructors (1):
    - mk: (inv : Invertible (denom : α)) (eq : a = num * ⅟(denom : α))

中文:
归纳类型 是有理数
  参数: [环 α] (a : α) (num : 整数) (denom : 自然数)
  构造子 (1 个):
    - mk: (inv : 可逆 (denom : α)) (eq : a = num * ⅟(denom : α))
-/
inductive IsRat [Ring α] (a : α) (num : Int) (denom : Nat) : Prop
  | mk (inv : Invertible (denom : α)) (eq : a = num * ⅟(denom : α))

/--
Inductive type `IsNNRat` / 归纳类型 `IsNNRat`

English:
inductive IsNNRat
  parameters: [Semiring α] (a : α) (num : Nat) (denom : Nat)
  constructors (1):
    - mk: (inv : Invertible (denom : α)) (eq : a = num * ⅟(denom : α))

中文:
归纳类型 是NNRat
  参数: [半环 α] (a : α) (num : 自然数) (denom : 自然数)
  构造子 (1 个):
    - mk: (inv : 可逆 (denom : α)) (eq : a = num * ⅟(denom : α))
-/
inductive IsNNRat [Semiring α] (a : α) (num : Nat) (denom : Nat) : Prop
  | mk (inv : Invertible (denom : α)) (eq : a = num * ⅟(denom : α))

/--
A "raw nnrat cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(NNRat.rawCast n d : α)` where `n` is a raw nat literal, `d` is a raw nat literal, and `d` is not
  `1` or `0`.

This representation is used by tactics like `ring` to decrease the number of typeclass arguments
required in each use of a number literal at type `α`.
-/
@[simp]
/--
Definition of `_root_.NNRat.rawCast` / `_root_.NNRat.rawCast` 的定义

English:
definition _root_.NNRat.rawCast
  signature: [DivisionSemiring α] (n : Nat) (d : Nat)
  body: n / d

中文:
定义 _root_.NNRat.rawCast
  签名: [除半环 α] (n : 自然数) (d : 自然数)
  定义体: n / d
-/
def _root_.NNRat.rawCast [DivisionSemiring α] (n : Nat) (d : Nat) : α := n / d

/--
A "raw rat cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural number literal
* `(NNRat.rawCast n d : α)` where `n` is a raw nat literal, `d` is a raw nat literal, and `d` is not
  `1` or `0`.
* `(Rat.rawCast (Int.negOfNat n) d : α)` where `n` is a raw nat literal,
  `d` is a raw nat literal, `n` is not `0`, and `d` is not `1` or `0`.

This representation is used by tactics like `ring` to decrease the number of typeclass arguments
required in each use of a number literal at type `α`.
-/
@[simp]
/--
Definition of `_root_.Rat.rawCast` / `_root_.Rat.rawCast` 的定义

English:
definition _root_.Rat.rawCast
  signature: [DivisionRing α] (n : Int) (d : Nat)
  body: n / d

中文:
定义 _root_.有理数.rawCast
  签名: [除环 α] (n : 整数) (d : 自然数)
  定义体: n / d
-/
def _root_.Rat.rawCast [DivisionRing α] (n : Int) (d : Nat) : α := n / d

/--
theorem `IsNNRat.to_isNat` / 定理 `IsNNRat.to_isNat`

English:
theorem IsNNRat.to_isNat
  given: {α} [Semiring α]
  statement: forall {a : α} {n}, IsNNRat a (n) (nat_lit 1) -> IsNat a n
  proof: @invertibleOne α _; ⟨by simp⟩

中文:
定理 是NNRat.to_is自然数
  条件: {α} [半环 α]
  结论: 对任意 {a : α} {n}, 是NNRat a (n) (nat_lit 1) -> 是自然数 a n
  证明: @invertibleOne α _; ⟨by simp⟩

Depends on / 依赖: invertibleOne
-/
theorem IsNNRat.to_isNat {α} [Semiring α] : forall {a : α} {n}, IsNNRat a (n) (nat_lit 1) -> IsNat a n
  | _, num, ⟨inv, rfl⟩ => have := @invertibleOne α _; ⟨by simp⟩

/--
theorem `IsRat.to_isNNRat` / 定理 `IsRat.to_isNNRat`

English:
theorem IsRat.to_isNNRat
  given: {α} [Ring α]
  statement: forall {a : α} {n d}, IsRat a (.ofNat n) (d) -> IsNNRat a n d

中文:
定理 是有理数.to_isNNRat
  条件: {α} [环 α]
  结论: 对任意 {a : α} {n d}, 是有理数 a (.of自然数 n) (d) -> 是NNRat a n d
-/
theorem IsRat.to_isNNRat {α} [Ring α] : forall {a : α} {n d}, IsRat a (.ofNat n) (d) -> IsNNRat a n d
  | _, _, _, ⟨inv, rfl⟩ => ⟨inv, by simp⟩

/--
theorem `IsNat.to_isNNRat` / 定理 `IsNat.to_isNNRat`

English:
theorem IsNat.to_isNNRat
  given: {α} [Semiring α]
  statement: forall {a : α} {n}, IsNat a n -> IsNNRat a (n) (nat_lit 1)

中文:
定理 是自然数.to_isNNRat
  条件: {α} [半环 α]
  结论: 对任意 {a : α} {n}, 是自然数 a n -> 是NNRat a (n) (nat_lit 1)
-/
theorem IsNat.to_isNNRat {α} [Semiring α] : forall {a : α} {n}, IsNat a n -> IsNNRat a (n) (nat_lit 1)
  | _, _, ⟨rfl⟩ => ⟨⟨1, by simp, by simp⟩, by simp⟩

/--
theorem `IsNNRat.to_isRat` / 定理 `IsNNRat.to_isRat`

English:
theorem IsNNRat.to_isRat
  given: {α} [Ring α]
  statement: forall {a : α} {n d}, IsNNRat a n d -> IsRat a (.ofNat n) d

中文:
定理 是NNRat.to_isRat
  条件: {α} [环 α]
  结论: 对任意 {a : α} {n d}, 是NNRat a n d -> 是有理数 a (.of自然数 n) d
-/
theorem IsNNRat.to_isRat {α} [Ring α] : forall {a : α} {n d}, IsNNRat a n d -> IsRat a (.ofNat n) d
  | _, _, _, ⟨inv, rfl⟩ => ⟨inv, by simp⟩

/--
theorem `IsRat.to_isInt` / 定理 `IsRat.to_isInt`

English:
theorem IsRat.to_isInt
  given: {α} [Ring α]
  statement: forall {a : α} {n}, IsRat a n (nat_lit 1) -> IsInt a n
  proof: @invertibleOne α _; ⟨by simp⟩

中文:
定理 是有理数.to_is整数
  条件: {α} [环 α]
  结论: 对任意 {a : α} {n}, 是有理数 a n (nat_lit 1) -> 是整数 a n
  证明: @invertibleOne α _; ⟨by simp⟩

Depends on / 依赖: invertibleOne
-/
theorem IsRat.to_isInt {α} [Ring α] : forall {a : α} {n}, IsRat a n (nat_lit 1) -> IsInt a n
  | _, _, ⟨inv, rfl⟩ => have := @invertibleOne α _; ⟨by simp⟩

/--
theorem `IsInt.to_isRat` / 定理 `IsInt.to_isRat`

English:
theorem IsInt.to_isRat
  given: {α} [Ring α]
  statement: forall {a : α} {n}, IsInt a n -> IsRat a n (nat_lit 1)

中文:
定理 是整数.to_isRat
  条件: {α} [环 α]
  结论: 对任意 {a : α} {n}, 是整数 a n -> 是有理数 a n (nat_lit 1)
-/
theorem IsInt.to_isRat {α} [Ring α] : forall {a : α} {n}, IsInt a n -> IsRat a n (nat_lit 1)
  | _, _, ⟨rfl⟩ => ⟨⟨1, by simp, by simp⟩, by simp⟩

/--
theorem `IsNNRat.to_raw_eq` / 定理 `IsNNRat.to_raw_eq`

English:
theorem IsNNRat.to_raw_eq
  given: {n d : Nat} [DivisionSemiring α]

中文:
定理 是NNRat.to_raw_eq
  条件: {n d : 自然数} [除半环 α]
-/
theorem IsNNRat.to_raw_eq {n d : Nat} [DivisionSemiring α] :
    forall {a}, IsNNRat (a : α) n d -> a = NNRat.rawCast n d
  | _, ⟨inv, rfl⟩ => by simp [div_eq_mul_inv]

/--
theorem `IsRat.to_raw_eq` / 定理 `IsRat.to_raw_eq`

English:
theorem IsRat.to_raw_eq
  given: {n : Int} {d : Nat} [DivisionRing α]

中文:
定理 是有理数.to_raw_eq
  条件: {n : 整数} {d : 自然数} [除环 α]
-/
theorem IsRat.to_raw_eq {n : Int} {d : Nat} [DivisionRing α] :
    forall {a}, IsRat (a : α) n d -> a = Rat.rawCast n d
  | _, ⟨inv, rfl⟩ => by simp [div_eq_mul_inv]

/--
theorem `IsRat.neg_to_eq` / 定理 `IsRat.neg_to_eq`

English:
theorem IsRat.neg_to_eq
  given: {α} [DivisionRing α] {n d}

中文:
定理 是有理数.neg_to_eq
  条件: {α} [除环 α] {n d}
-/
theorem IsRat.neg_to_eq {α} [DivisionRing α] {n d} :
    {a n' d' : α} -> IsRat a (.negOfNat n) d -> n = n' -> d = d' -> a = -(n' / d')
  | _, _, _, ⟨_, rfl⟩, rfl, rfl => by simp [div_eq_mul_inv]

/--
theorem `IsNNRat.to_eq` / 定理 `IsNNRat.to_eq`

English:
theorem IsNNRat.to_eq
  given: {α} [DivisionSemiring α] {n d}

中文:
定理 是NNRat.to_eq
  条件: {α} [除半环 α] {n d}
-/
theorem IsNNRat.to_eq {α} [DivisionSemiring α] {n d} :
    {a n' d' : α} -> IsNNRat a n d -> n = n' -> d = d' -> a = n' / d'
  | _, _, _, ⟨_, rfl⟩, rfl, rfl => by simp [div_eq_mul_inv]

/--
theorem `IsNNRat.of_raw` / 定理 `IsNNRat.of_raw`

English:
theorem IsNNRat.of_raw
  statement: (α) [DivisionSemiring α] (n : Nat) (d : Nat)
  proof: have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩

中文:
定理 是NNRat.of_raw
  结论: (α) [除半环 α] (n : 自然数) (d : 自然数)
  证明: have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩

Depends on / 依赖: div_eq_mul_inv, invertibleOfNonzero
-/
theorem IsNNRat.of_raw (α) [DivisionSemiring α] (n : Nat) (d : Nat)
    (h : (d : α) != 0) : IsNNRat (NNRat.rawCast n d : α) n d :=
  have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩

/--
theorem `IsRat.of_raw` / 定理 `IsRat.of_raw`

English:
theorem IsRat.of_raw
  statement: (α) [DivisionRing α] (n : Int) (d : Nat)
  proof: have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩

中文:
定理 是有理数.of_raw
  结论: (α) [除环 α] (n : 整数) (d : 自然数)
  证明: have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩

Depends on / 依赖: div_eq_mul_inv, invertibleOfNonzero
-/
theorem IsRat.of_raw (α) [DivisionRing α] (n : Int) (d : Nat)
    (h : (d : α) != 0) : IsRat (Rat.rawCast n d : α) n d :=
  have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩

/--
theorem `IsNNRat.den_nz` / 定理 `IsNNRat.den_nz`

English:
theorem IsNNRat.den_nz
  given: {α} [DivisionSemiring α] {a n d}
  statement: IsNNRat (a : α) n d -> (d : α) != 0

中文:
定理 是NNRat.den_nz
  条件: {α} [除半环 α] {a n d}
  结论: 是NNRat (a : α) n d -> (d : α) != 0
-/
theorem IsNNRat.den_nz {α} [DivisionSemiring α] {a n d} : IsNNRat (a : α) n d -> (d : α) != 0
  | ⟨_, _⟩ => Invertible.ne_zero (d : α)

/--
theorem `IsRat.den_nz` / 定理 `IsRat.den_nz`

English:
theorem IsRat.den_nz
  given: {α} [DivisionRing α] {a n d}
  statement: IsRat (a : α) n d -> (d : α) != 0

中文:
定理 是有理数.den_nz
  条件: {α} [除环 α] {a n d}
  结论: 是有理数 (a : α) n d -> (d : α) != 0
-/
theorem IsRat.den_nz {α} [DivisionRing α] {a n d} : IsRat (a : α) n d -> (d : α) != 0
  | ⟨_, _⟩ => Invertible.ne_zero (d : α)

meta section

/--
Inductive type `Result'` / 归纳类型 `Result'`

English:
inductive Result'
  parameters: where
  constructors (5):
    - isBool: (val : Bool) (proof : Expr)
    - isNat: (inst lit proof : Expr)
    - isNegNat: (inst lit proof : Expr)
    - isNNRat: (inst : Expr) (q : Rat) (n d proof : Expr)
    - isNegNNRat: (inst : Expr) (q : Rat) (n d proof : Expr)

中文:
归纳类型 Result'
  参数: where
  构造子 (5 个):
    - isBool: (val : 布尔值) (proof : Expr)
    - isNat: (inst lit proof : Expr)
    - isNegNat: (inst lit proof : Expr)
    - isNNRat: (inst : Expr) (q : 有理数) (n d proof : Expr)
    - isNegNNRat: (inst : Expr) (q : 有理数) (n d proof : Expr)
-/
inductive Result' where
  /-- Untyped version of `Result.isBool`. -/
  | isBool (val : Bool) (proof : Expr)
  /-- Untyped version of `Result.isNat`. -/
  | isNat (inst lit proof : Expr)
  /-- Untyped version of `Result.isNegNat`. -/
  | isNegNat (inst lit proof : Expr)
  /-- Untyped version of `Result.isNNRat`. -/
  | isNNRat (inst : Expr) (q : Rat) (n d proof : Expr)
  /-- Untyped version of `Result.isNegNNRat`. -/
  | isNegNNRat (inst : Expr) (q : Rat) (n d proof : Expr)
  deriving Inhabited

section
set_option linter.unusedVariables false

/--
Definition of `Result` / `Result` 的定义

English:
definition Result
  signature: {α : Q(Type u)} (x : Q($α))
  body: Result'

中文:
定义 Result
  签名: {α : Q(类型u)} (x : Q($α))
  定义体: Result'
-/
@[nolint unusedArguments] def Result {α : Q(Type u)} (x : Q($α)) := Result'

-- The new behaviour of `inferInstanceAs` from leanprover/lean4#12897 needs to be updated,
-- to ensure that if we are in a `meta` section then the auxiliary definitions are also `meta`.
-- Fixed in https://github.com/leanprover/lean4/pull/13043
instance {α : Q(Type u)} {x : Q($α)} : Inhabited (Result x) := inferInstanceAs (Inhabited Result')

/--
Definition of `Result.isTrue` / `Result.isTrue` 的定义

English:
definition Result.isTrue
  signature: {x : Q(Prop)}
  body: Result'.isBool true

中文:
定义 Result.isTrue
  签名: {x : Q(命题)}
  定义体: Result'.isBool true
-/
@[match_pattern, inline] def Result.isTrue {x : Q(Prop)} :
    forall (proof : Q($x)), Result q($x) := Result'.isBool true

/--
Definition of `Result.isFalse` / `Result.isFalse` 的定义

English:
definition Result.isFalse
  signature: {x : Q(Prop)}
  body: Result'.isBool false

中文:
定义 Result.isFalse
  签名: {x : Q(命题)}
  定义体: Result'.isBool false
-/
@[match_pattern, inline] def Result.isFalse {x : Q(Prop)} :
    forall (proof : Q(¬$x)), Result q($x) := Result'.isBool false

/--
Definition of `Result.isNat` / `Result.isNat` 的定义

English:
definition Result.isNat
  signature: {α : Q(Type u)} {x : Q($α)}
  body: Result'.isNat

中文:
定义 Result.is自然数
  签名: {α : Q(类型u)} {x : Q($α)}
  定义体: Result'.isNat
-/
@[match_pattern, inline] def Result.isNat {α : Q(Type u)} {x : Q($α)} :
    forall (inst : Q(AddMonoidWithOne $α) := by assumption) (lit : Q(Nat)) (proof : Q(IsNat $x $lit)),
      Result x := Result'.isNat

/--
Definition of `Result.isNegNat` / `Result.isNegNat` 的定义

English:
definition Result.isNegNat
  signature: {α : Q(Type u)} {x : Q($α)}
  body: Result'.isNegNat

中文:
定义 Result.isNeg自然数
  签名: {α : Q(类型u)} {x : Q($α)}
  定义体: Result'.isNegNat
-/
@[match_pattern, inline] def Result.isNegNat {α : Q(Type u)} {x : Q($α)} :
    forall (inst : Q(Ring $α) := by assumption) (lit : Q(Nat)) (proof : Q(IsInt $x (.negOfNat $lit))),
      Result x := Result'.isNegNat

/--
Definition of `Result.isNNRat` / `Result.isNNRat` 的定义

English:
definition Result.isNNRat
  signature: {α : Q(Type u)} {x : Q($α)}
  body: Result'.isNNRat

中文:
定义 Result.isNNRat
  签名: {α : Q(类型u)} {x : Q($α)}
  定义体: Result'.isNNRat
-/
@[match_pattern, inline] def Result.isNNRat {α : Q(Type u)} {x : Q($α)} :
    forall (inst : Q(DivisionSemiring $α) := by assumption) (q : Rat) (n : Q(Nat)) (d : Q(Nat))
      (proof : Q(IsNNRat $x $n $d)), Result x := Result'.isNNRat

/--
Definition of `Result.isNegNNRat` / `Result.isNegNNRat` 的定义

English:
definition Result.isNegNNRat
  signature: {α : Q(Type u)} {x : Q($α)}
  body: Result'.isNegNNRat

中文:
定义 Result.isNegNNRat
  签名: {α : Q(类型u)} {x : Q($α)}
  定义体: Result'.isNegNNRat
-/
@[match_pattern, inline] def Result.isNegNNRat {α : Q(Type u)} {x : Q($α)} :
    forall (inst : Q(DivisionRing $α) := by assumption) (q : Rat) (n : Q(Nat)) (d : Q(Nat))
      (proof : Q(IsRat $x (.negOfNat $n) $d)), Result x := Result'.isNegNNRat

end

-- Note the independent arguments `z : Q(ℤ)` and `n : ℤ`.
-- We ensure these are "the same" when calling.
/--
Definition of `Result.isInt` / `Result.isInt` 的定义

English:
definition Result.isInt
  signature: {α : Q(Type u)} {x : Q($α)} (inst : Q(Ring $α) := by assumption)
  body: have lit : Q(Nat) := z.appArg!
  if 0 <= n then
    let proof : Q(IsInt $x (.ofNat $lit)) := proof
    .isNat q(instAddMonoidWithOne) lit q(IsInt.to_isNat $proof)
  else
    .isNegNat inst lit proof

中文:
定义 Result.is整数
  签名: {α : Q(类型u)} {x : Q($α)} (inst : Q(环 $α) := by assumption)
  定义体: have lit : Q(Nat) := z.appArg!
  if 0 <= n then
    let proof : Q(IsInt $x (.ofNat $lit)) := proof
    .isNat q(instAddMonoidWithOne) lit q(IsInt.to_isNat $proof)
  else
    .isNegNat inst lit proof

Depends on / 依赖: IsInt.to_isNat, Result, appArg, instAddMonoidWithOne, isNegNat, to_isNat, z.appArg
-/
def Result.isInt {α : Q(Type u)} {x : Q($α)} (inst : Q(Ring $α) := by assumption)
    (z : Q(Int)) (n : Int) (proof : Q(IsInt $x $z)) : Result x :=
  have lit : Q(Nat) := z.appArg!
  if 0 <= n then
    let proof : Q(IsInt $x (.ofNat $lit)) := proof
    .isNat q(instAddMonoidWithOne) lit q(IsInt.to_isNat $proof)
  else
    .isNegNat inst lit proof

-- Note the independent arguments `q : Q(ℚ)` and `n : ℚ`.
-- We ensure these are "the same" when calling.
/--
Definition of `Result.isNNRat'` / `Result.isNNRat'` 的定义

English:
definition Result.isNNRat'
  signature: {α : Q(Type u)} {x : Q($α)} (inst : Q(DivisionSemiring $α) := by assumption)
  body: if q.den = 1 then
haveI : nat_lit 1 =Q d := ⟨⟩
    .isNat q(instAddMonoidWithOne') n q(IsNNRat.to_isNat $proof)
  else
    .isNNRat inst q n d proof

中文:
定义 Result.isNNRat'
  签名: {α : Q(类型u)} {x : Q($α)} (inst : Q(除半环 $α) := by assumption)
  定义体: if q.den = 1 then
haveI : nat_lit 1 =Q d := ⟨⟩
    .isNat q(instAddMonoidWithOne') n q(IsNNRat.to_isNat $proof)
  else
    .isNNRat inst q n d proof

Depends on / 依赖: IsNNRat, IsNNRat.to_isNat, Result, instAddMonoidWithOne, isNNRat, nat_lit, q.den, to_isNat
-/
def Result.isNNRat' {α : Q(Type u)} {x : Q($α)} (inst : Q(DivisionSemiring $α) := by assumption)
    (q : Rat) (n : Q(Nat)) (d : Q(Nat)) (proof : Q(IsNNRat $x $n $d)) : Result x :=
  if q.den = 1 then
haveI : nat_lit 1 =Q d := ⟨⟩
    .isNat q(instAddMonoidWithOne') n q(IsNNRat.to_isNat $proof)
  else
    .isNNRat inst q n d proof

-- Note the independent arguments `q : Q(ℚ)` and `n : ℚ`.
-- We ensure these are "the same" when calling.
/--
Definition of `Result.isRat` / `Result.isRat` 的定义

English:
definition Result.isRat
  signature: {α : Q(Type u)} {x : Q($α)} (inst : Q(DivisionRing $α) := by assumption)
  body: have lit : Q(Nat) := n.appArg!
  if q.den = 1 then
    have proof : Q(IsRat $x $n (nat_lit 1)) := proof
    .isInt q(DivisionRing.toRing) n q.num q(IsRat.to_isInt $proof)
  else if 0 <= q then
    let proof : Q(IsRat $x (.ofNat $lit) $d) := proof
    .isNNRat q(DivisionRing.toDivisionSemiring) q lit d q(IsRat.to_isNNRat $proof)
  else
    .isNegNNRat inst q lit d proof

中文:
定义 Result.isRat
  签名: {α : Q(类型u)} {x : Q($α)} (inst : Q(除环 $α) := by assumption)
  定义体: have lit : Q(Nat) := n.appArg!
  if q.den = 1 then
    have proof : Q(IsRat $x $n (nat_lit 1)) := proof
    .isInt q(DivisionRing.toRing) n q.num q(IsRat.to_isInt $proof)
  else if 0 <= q then
    let proof : Q(IsRat $x (.ofNat $lit) $d) := proof
    .isNNRat q(DivisionRing.toDivisionSemiring) q lit d q(IsRat.to_isNNRat $proof)
  else
    .isNegNNRat inst q lit d proof

Depends on / 依赖: DivisionRing, DivisionRing.toDivisionSemiring, DivisionRing.toRing, IsRat.to_isInt, IsRat.to_isNNRat, Result, appArg, isNNRat, isNegNNRat, n.appArg, nat_lit, q.den, q.num, toDivisionSemiring, toRing, to_isInt, to_isNNRat
-/
def Result.isRat {α : Q(Type u)} {x : Q($α)} (inst : Q(DivisionRing $α) := by assumption)
    (q : Rat) (n : Q(Int)) (d : Q(Nat)) (proof : Q(IsRat $x $n $d)) : Result x :=
  have lit : Q(Nat) := n.appArg!
  if q.den = 1 then
    have proof : Q(IsRat $x $n (nat_lit 1)) := proof
    .isInt q(DivisionRing.toRing) n q.num q(IsRat.to_isInt $proof)
  else if 0 <= q then
    let proof : Q(IsRat $x (.ofNat $lit) $d) := proof
    .isNNRat q(DivisionRing.toDivisionSemiring) q lit d q(IsRat.to_isNNRat $proof)
  else
    .isNegNNRat inst q lit d proof


instance {α : Q(Type u)} {x : Q($α)} : ToMessageData (Result x) where
  toMessageData
  | .isBool true proof => m!"isTrue ({proof})"
  | .isBool false proof => m!"isFalse ({proof})"
  | .isNat _ lit proof => m!"isNat {lit} ({proof})"
  | .isNegNat _ lit proof => m!"isNegNat {lit} ({proof})"
  | .isNNRat _ q _ _ proof => m!"isNNRat {q} ({proof})"
  | .isNegNNRat _ q _ _ proof => m!"isNegNNRat {q} ({proof})"

/--
Definition of `Result.toRat` / `Result.toRat` 的定义

English:
definition Result.toRat
  signature: {α : Q(Type u)} {e : Q($α)}

中文:
定义 Result.toRat
  签名: {α : Q(类型u)} {e : Q($α)}
-/
def Result.toRat {α : Q(Type u)} {e : Q($α)} : Result e -> Option Rat
  | .isBool .. => none
  | .isNat _ lit _ => some lit.natLit!
  | .isNegNat _ lit _ => some (-lit.natLit!)
  | .isNNRat _ q .. => some q
  | .isNegNNRat _ q .. => some q

/--
Definition of `Result.toRatNZ` / `Result.toRatNZ` 的定义

English:
definition Result.toRatNZ
  signature: {α : Q(Type u)} {e : Q($α)}

中文:
定义 Result.toRatNZ
  签名: {α : Q(类型u)} {e : Q($α)}
-/
def Result.toRatNZ {α : Q(Type u)} {e : Q($α)} : Result e -> Option (Rat × Option Expr)
  | .isBool .. => none
  | .isNat _ lit _ => some (lit.natLit!, none)
  | .isNegNat _ lit _ => some (-lit.natLit!, none)
  | .isNNRat _ q _ _ p => some (q, q(IsNNRat.den_nz $p))
  | .isNegNNRat _ q _ _ p => some (q, q(IsRat.den_nz $p))

/--
Definition of `Result.toInt` / `Result.toInt` 的定义

English:
definition Result.toInt
  signature: {α : Q(Type u)} {e : Q($α)} (_i : Q(Ring $α) := by with_reducible assumption)
  body: proof
    pure ⟨lit.natLit!, q(.ofNat $lit), q(($proof).to_isInt)⟩
  | .isNegNat _ lit proof => pure ⟨-lit.natLit!, q(.negOfNat $lit), proof⟩
  | _ => failure

中文:
定义 Result.to整数
  签名: {α : Q(类型u)} {e : Q($α)} (_i : Q(环 $α) := by with_reducible assumption)
  定义体: proof
    pure ⟨lit.natLit!, q(.ofNat $lit), q(($proof).to_isInt)⟩
  | .isNegNat _ lit proof => pure ⟨-lit.natLit!, q(.negOfNat $lit), proof⟩
  | _ => failure

Depends on / 依赖: Result, failure, instAddMonoidWithOne, isNegNat, lit.natLit, natLit, negOfNat, to_isInt, with_reducible
-/
def Result.toInt {α : Q(Type u)} {e : Q($α)} (_i : Q(Ring $α) := by with_reducible assumption) :
    Result e -> Option (Int × (lit : Q(Int)) × Q(IsInt $e $lit))
  | .isNat _ lit proof => do
    have proof : Q(@IsNat _ instAddMonoidWithOne $e $lit) := proof
    pure ⟨lit.natLit!, q(.ofNat $lit), q(($proof).to_isInt)⟩
  | .isNegNat _ lit proof => pure ⟨-lit.natLit!, q(.negOfNat $lit), proof⟩
  | _ => failure

/--
Definition of `Result.toNNRat'` / `Result.toNNRat'` 的定义

English:
definition Result.toNNRat'
  signature: {α : Q(Type u)} {e : Q($α)}
  body: proof
    some ⟨lit.natLit!, q($lit), q(nat_lit 1), q(($proof).to_isNNRat)⟩
  | .isNNRat _ q n d proof => some ⟨q, n, d, proof⟩
  | _ => none

中文:
定义 Result.toNNRat'
  签名: {α : Q(类型u)} {e : Q($α)}
  定义体: proof
    some ⟨lit.natLit!, q($lit), q(nat_lit 1), q(($proof).to_isNNRat)⟩
  | .isNNRat _ q n d proof => some ⟨q, n, d, proof⟩
  | _ => none

Depends on / 依赖: IsNNRat, Result, instAddMonoidWithOne, isNNRat, lit.natLit, natLit, nat_lit, to_isNNRat, with_reducible
-/
def Result.toNNRat' {α : Q(Type u)} {e : Q($α)}
    (_i : Q(DivisionSemiring $α) := by with_reducible assumption) :
    Result e -> Option (Rat × (n : Q(Nat)) × (d : Q(Nat)) × Q(IsNNRat $e $n $d))
  | .isNat _ lit proof =>
    have proof : Q(@IsNat _ instAddMonoidWithOne' $e $lit) := proof
    some ⟨lit.natLit!, q($lit), q(nat_lit 1), q(($proof).to_isNNRat)⟩
  | .isNNRat _ q n d proof => some ⟨q, n, d, proof⟩
  | _ => none

/--
Definition of `Result.toRat'` / `Result.toRat'` 的定义

English:
definition Result.toRat'
  signature: {α : Q(Type u)} {e : Q($α)}
  body: proof
    some ⟨lit.natLit!, q(.ofNat $lit), q(nat_lit 1), q(($proof).to_isNNRat.to_isRat)⟩
  | .isNegNat _ lit proof =>
    have proof : Q(@IsInt _ DivisionRing.toRing $e (.negOfNat $lit)) := proof
    some ⟨-lit.natLit!, q(.negOfNat $lit), q(nat_lit 1),
      q(@IsInt.to_isRat _ DivisionRing.toRing _ _ $proof)⟩
  | .isNNRat inst q n d proof =>
letI : inst =Q DivisionRing.toDivisionSemiring := ⟨⟩
    some ⟨q, q(.ofNat $n), d, q(IsNNRat.to_isRat $proof)⟩
  | .isNegNNRat _ q n d proof => some ⟨q, q(.negOfNat $n), d, proof⟩

中文:
定义 Result.toRat'
  签名: {α : Q(类型u)} {e : Q($α)}
  定义体: proof
    some ⟨lit.natLit!, q(.ofNat $lit), q(nat_lit 1), q(($proof).to_isNNRat.to_isRat)⟩
  | .isNegNat _ lit proof =>
    have proof : Q(@IsInt _ DivisionRing.toRing $e (.negOfNat $lit)) := proof
    some ⟨-lit.natLit!, q(.negOfNat $lit), q(nat_lit 1),
      q(@IsInt.to_isRat _ DivisionRing.toRing _ _ $proof)⟩
  | .isNNRat inst q n d proof =>
letI : inst =Q DivisionRing.toDivisionSemiring := ⟨⟩
    some ⟨q, q(.ofNat $n), d, q(IsNNRat.to_isRat $proof)⟩
  | .isNegNNRat _ q n d proof => some ⟨q, q(.negOfNat $n), d, proof⟩

Depends on / 依赖: DivisionRing, DivisionRing.toRing, IsInt.to_isRat, Result, instAddMonoidWithOne, isBool, isNegNat, lit.natLit, natLit, nat_lit, negOfNat, toRing, to_isNNRat, to_isNNRat.to_isRat, to_isRat, with_reducible
-/
def Result.toRat' {α : Q(Type u)} {e : Q($α)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) :
    Result e -> Option (Rat × (n : Q(Int)) × (d : Q(Nat)) × Q(IsRat $e $n $d))
  | .isBool .. => none
  | .isNat _ lit proof =>
    have proof : Q(@IsNat _ instAddMonoidWithOne $e $lit) := proof
    some ⟨lit.natLit!, q(.ofNat $lit), q(nat_lit 1), q(($proof).to_isNNRat.to_isRat)⟩
  | .isNegNat _ lit proof =>
    have proof : Q(@IsInt _ DivisionRing.toRing $e (.negOfNat $lit)) := proof
    some ⟨-lit.natLit!, q(.negOfNat $lit), q(nat_lit 1),
      q(@IsInt.to_isRat _ DivisionRing.toRing _ _ $proof)⟩
  | .isNNRat inst q n d proof =>
letI : inst =Q DivisionRing.toDivisionSemiring := ⟨⟩
    some ⟨q, q(.ofNat $n), d, q(IsNNRat.to_isRat $proof)⟩
  | .isNegNNRat _ q n d proof => some ⟨q, q(.negOfNat $n), d, proof⟩

/--
Definition of `Result.toRawEq` / `Result.toRawEq` 的定义

English:
definition Result.toRawEq
  signature: {α : Q(Type u)} {e : Q($α)}
  body: e; have p : Q(¬$e) := p
    ⟨(q(False) : Expr), (q(eq_false $p) : Expr)⟩
  | .isBool true p =>
    have e : Q(Prop) := e; have p : Q($e) := p
    ⟨(q(True) : Expr), (q(eq_true $p) : Expr)⟩
  | .isNat _ lit p => ⟨q(Nat.rawCast $lit), q(IsNat.to_raw_eq $p)⟩
  | .isNegNat _ lit p => ⟨q(Int.rawCast (.negOfNat $lit)), q(IsInt.to_raw_eq $p)⟩
  | .isNNRat _ _ n d p => ⟨q(NNRat.rawCast $n $d), q(IsNNRat.to_raw_eq $p)⟩
  | .isNegNNRat _ _ n d p => ⟨q(Rat.rawCast (.negOfNat $n) $d), q(IsRat.to_raw_eq $p)⟩

中文:
定义 Result.toRawEq
  签名: {α : Q(类型u)} {e : Q($α)}
  定义体: e; have p : Q(¬$e) := p
    ⟨(q(False) : Expr), (q(eq_false $p) : Expr)⟩
  | .isBool true p =>
    have e : Q(Prop) := e; have p : Q($e) := p
    ⟨(q(True) : Expr), (q(eq_true $p) : Expr)⟩
  | .isNat _ lit p => ⟨q(Nat.rawCast $lit), q(IsNat.to_raw_eq $p)⟩
  | .isNegNat _ lit p => ⟨q(Int.rawCast (.negOfNat $lit)), q(IsInt.to_raw_eq $p)⟩
  | .isNNRat _ _ n d p => ⟨q(NNRat.rawCast $n $d), q(IsNNRat.to_raw_eq $p)⟩
  | .isNegNNRat _ _ n d p => ⟨q(Rat.rawCast (.negOfNat $n) $d), q(IsRat.to_raw_eq $p)⟩
-/
def Result.toRawEq {α : Q(Type u)} {e : Q($α)} : Result e -> (e' : Q($α)) × Q($e = $e')
  | .isBool false p =>
    have e : Q(Prop) := e; have p : Q(¬$e) := p
    ⟨(q(False) : Expr), (q(eq_false $p) : Expr)⟩
  | .isBool true p =>
    have e : Q(Prop) := e; have p : Q($e) := p
    ⟨(q(True) : Expr), (q(eq_true $p) : Expr)⟩
  | .isNat _ lit p => ⟨q(Nat.rawCast $lit), q(IsNat.to_raw_eq $p)⟩
  | .isNegNat _ lit p => ⟨q(Int.rawCast (.negOfNat $lit)), q(IsInt.to_raw_eq $p)⟩
  | .isNNRat _ _ n d p => ⟨q(NNRat.rawCast $n $d), q(IsNNRat.to_raw_eq $p)⟩
  | .isNegNNRat _ _ n d p => ⟨q(Rat.rawCast (.negOfNat $n) $d), q(IsRat.to_raw_eq $p)⟩

/--
Definition of `Result.toRawIntEq` / `Result.toRawIntEq` 的定义

English:
definition Result.toRawIntEq
  signature: {α : Q(Type u)} {e : Q($α)}

中文:
定义 Result.toRaw整数Eq
  签名: {α : Q(类型u)} {e : Q($α)}
-/
def Result.toRawIntEq {α : Q(Type u)} {e : Q($α)} : Result e ->
    Option (Int × (e' : Q($α)) × Q($e = $e'))
  | .isNat _ lit p => some ⟨lit.natLit!, q(Nat.rawCast $lit), q(IsNat.to_raw_eq $p)⟩
  | .isNegNat _ lit p => some ⟨-lit.natLit!, q(Int.rawCast (.negOfNat $lit)), q(IsInt.to_raw_eq $p)⟩
  | .isNNRat _ .. | .isNegNNRat _ .. | .isBool .. => none

/--
Definition of `Result.ofRawNat` / `Result.ofRawNat` 的定义

English:
definition Result.ofRawNat
  signature: {α : Q(Type u)} (e : Q($α))
  body: Id.run do
  let .app (.app _ (sα : Q(AddMonoidWithOne $α))) (lit : Q(Nat)) := e | panic! "not a raw nat cast"
  .isNat sα lit (q(IsNat.of_raw $α $lit) : Expr)

中文:
定义 Result.ofRaw自然数
  签名: {α : Q(类型u)} (e : Q($α))
  定义体: Id.run do
  let .app (.app _ (sα : Q(AddMonoidWithOne $α))) (lit : Q(Nat)) := e | panic! "not a raw nat cast"
  .isNat sα lit (q(IsNat.of_raw $α $lit) : Expr)

Depends on / 依赖: Id.run
-/
def Result.ofRawNat {α : Q(Type u)} (e : Q($α)) : Result e := Id.run do
  let .app (.app _ (sα : Q(AddMonoidWithOne $α))) (lit : Q(Nat)) := e | panic! "not a raw nat cast"
  .isNat sα lit (q(IsNat.of_raw $α $lit) : Expr)

/--
Definition of `Result.ofRawInt` / `Result.ofRawInt` 的定义

English:
definition Result.ofRawInt
  signature: {α : Q(Type u)} (n : Int) (e : Q($α))
  body: if 0 <= n then
    Result.ofRawNat e
  else Id.run do
    let .app (.app _ (rα : Q(Ring $α))) (.app _ (lit : Q(Nat))) := e | panic! "not a raw int cast"
    .isNegNat rα lit (q(IsInt.of_raw $α (.negOfNat $lit)) : Expr)

中文:
定义 Result.ofRaw整数
  签名: {α : Q(类型u)} (n : 整数) (e : Q($α))
  定义体: if 0 <= n then
    Result.ofRawNat e
  else Id.run do
    let .app (.app _ (rα : Q(Ring $α))) (.app _ (lit : Q(Nat))) := e | panic! "not a raw int cast"
    .isNegNat rα lit (q(IsInt.of_raw $α (.negOfNat $lit)) : Expr)

Depends on / 依赖: Id.run, IsInt.of_raw, Result, Result.ofRawNat, isNegNat, negOfNat, ofRawNat, of_raw
-/
def Result.ofRawInt {α : Q(Type u)} (n : Int) (e : Q($α)) : Result e :=
  if 0 <= n then
    Result.ofRawNat e
  else Id.run do
    let .app (.app _ (rα : Q(Ring $α))) (.app _ (lit : Q(Nat))) := e | panic! "not a raw int cast"
    .isNegNat rα lit (q(IsInt.of_raw $α (.negOfNat $lit)) : Expr)

/--
Definition of `Result.ofRawNNRat` / `Result.ofRawNNRat` 的定义

English:
definition Result.ofRawNNRat
  body: if q.den = 1 then
    Result.ofRawNat e
  else Id.run do
    let .app (.app (.app _ (dα : Q(DivisionSemiring $α))) (n : Q(Nat))) (d : Q(Nat)) := e
      | panic! "not a raw nnrat cast"
    let hyp : Q(($d : $α) != 0) := hyp.get!
    .isNNRat dα q n d (q(IsNNRat.of_raw $α $n $d $hyp) : Expr)

中文:
定义 Result.ofRawNNRat
  定义体: if q.den = 1 then
    Result.ofRawNat e
  else Id.run do
    let .app (.app (.app _ (dα : Q(DivisionSemiring $α))) (n : Q(Nat))) (d : Q(Nat)) := e
      | panic! "not a raw nnrat cast"
    let hyp : Q(($d : $α) != 0) := hyp.get!
    .isNNRat dα q n d (q(IsNNRat.of_raw $α $n $d $hyp) : Expr)

Depends on / 依赖: Result
-/
def Result.ofRawNNRat
    {α : Q(Type u)} (q : Rat) (e : Q($α)) (hyp : Option Expr := none) : Result e :=
  if q.den = 1 then
    Result.ofRawNat e
  else Id.run do
    let .app (.app (.app _ (dα : Q(DivisionSemiring $α))) (n : Q(Nat))) (d : Q(Nat)) := e
      | panic! "not a raw nnrat cast"
    let hyp : Q(($d : $α) != 0) := hyp.get!
    .isNNRat dα q n d (q(IsNNRat.of_raw $α $n $d $hyp) : Expr)

/--
Definition of `Result.ofRawRat` / `Result.ofRawRat` 的定义

English:
definition Result.ofRawRat
  signature: {α : Q(Type u)} (q : Rat) (e : Q($α)) (hyp : Option Expr := none)
  body: if q.den = 1 then
    Result.ofRawInt q.num e
  else if 0 <= q then
    Result.ofRawNNRat q e hyp
  else Id.run do
    let .app (.app (.app _ (dα : Q(DivisionRing $α))) (.app _ (n : Q(Nat)))) (d : Q(Nat)) := e
      | panic! "not a raw rat cast"
    let hyp : Q(($d : $α) != 0) := hyp.get!
    .isNegNNRat dα q n d (q(IsRat.of_raw $α (.negOfNat $n) $d $hyp) : Expr)

中文:
定义 Result.ofRawRat
  签名: {α : Q(类型u)} (q : 有理数) (e : Q($α)) (hyp : 选项类型 Expr := none)
  定义体: if q.den = 1 then
    Result.ofRawInt q.num e
  else if 0 <= q then
    Result.ofRawNNRat q e hyp
  else Id.run do
    let .app (.app (.app _ (dα : Q(DivisionRing $α))) (.app _ (n : Q(Nat)))) (d : Q(Nat)) := e
      | panic! "not a raw rat cast"
    let hyp : Q(($d : $α) != 0) := hyp.get!
    .isNegNNRat dα q n d (q(IsRat.of_raw $α (.negOfNat $n) $d $hyp) : Expr)

Depends on / 依赖: Result
-/
def Result.ofRawRat {α : Q(Type u)} (q : Rat) (e : Q($α)) (hyp : Option Expr := none) : Result e :=
  if q.den = 1 then
    Result.ofRawInt q.num e
  else if 0 <= q then
    Result.ofRawNNRat q e hyp
  else Id.run do
    let .app (.app (.app _ (dα : Q(DivisionRing $α))) (.app _ (n : Q(Nat)))) (d : Q(Nat)) := e
      | panic! "not a raw rat cast"
    let hyp : Q(($d : $α) != 0) := hyp.get!
    .isNegNNRat dα q n d (q(IsRat.of_raw $α (.negOfNat $n) $d $hyp) : Expr)

/--
Definition of `Result.toSimpResult` / `Result.toSimpResult` 的定义

English:
definition Result.toSimpResult
  signature: {α : Q(Type u)} {e : Q($α)}
  body: r.toRawEq; pure { expr, proof? }
  | .isNat sα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α sα lit
    return { expr := a', proof? := q(IsNat.to_eq $p $pa') }
  | .isNegNat _rα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) lit
    return { expr := q(-$a'), proof? := q(IsInt.neg_to_eq $p $pa') }
  | .isNNRat _ _ n d p => do
    let ⟨n', pn'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) n
    let ⟨d', pd'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) d
    return { expr := q($n' / $d'), proof? := q(IsNNRat.to_eq $p $pn' $pd') }
  | .isNegNNRat _ _ n d p => do
    let ⟨n', pn'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) n
    let ⟨d', pd'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) d
    return { expr := q(-($n' / $d')), proof? := q(IsRat.neg_to_eq $p $pn' $pd') }

中文:
定义 Result.toSimpResult
  签名: {α : Q(类型u)} {e : Q($α)}
  定义体: r.toRawEq; pure { expr, proof? }
  | .isNat sα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α sα lit
    return { expr := a', proof? := q(IsNat.to_eq $p $pa') }
  | .isNegNat _rα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) lit
    return { expr := q(-$a'), proof? := q(IsInt.neg_to_eq $p $pa') }
  | .isNNRat _ _ n d p => do
    let ⟨n', pn'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) n
    let ⟨d', pd'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) d
    return { expr := q($n' / $d'), proof? := q(IsNNRat.to_eq $p $pn' $pd') }
  | .isNegNNRat _ _ n d p => do
    let ⟨n', pn'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) n
    let ⟨d', pd'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) d
    return { expr := q(-($n' / $d')), proof? := q(IsRat.neg_to_eq $p $pn' $pd') }

Depends on / 依赖: r.toRawEq, toRawEq
-/
def Result.toSimpResult {α : Q(Type u)} {e : Q($α)} : Result e -> MetaM Simp.Result
  | r@(.isBool ..) => let ⟨expr, proof?⟩ := r.toRawEq; pure { expr, proof? }
  | .isNat sα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α sα lit
    return { expr := a', proof? := q(IsNat.to_eq $p $pa') }
  | .isNegNat _rα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) lit
    return { expr := q(-$a'), proof? := q(IsInt.neg_to_eq $p $pa') }
  | .isNNRat _ _ n d p => do
    let ⟨n', pn'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) n
    let ⟨d', pd'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) d
    return { expr := q($n' / $d'), proof? := q(IsNNRat.to_eq $p $pn' $pd') }
  | .isNegNNRat _ _ n d p => do
    let ⟨n', pn'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) n
    let ⟨d', pd'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) d
    return { expr := q(-($n' / $d')), proof? := q(IsRat.neg_to_eq $p $pn' $pd') }

/--
Definition of `BoolResult` / `BoolResult` 的定义

English:
abbreviation BoolResult
  signature: (p : Q(Prop)) (b : Bool)
  body: Q(Bool.rec (¬ $p) ($p) $b)

中文:
缩写 布尔Result
  签名: (p : Q(命题)) (b : 布尔值)
  定义体: Q(Bool.rec (¬ $p) ($p) $b)

Depends on / 依赖: Bool.rec
-/
abbrev BoolResult (p : Q(Prop)) (b : Bool) : Type :=
  Q(Bool.rec (¬ $p) ($p) $b)

/--
Definition of `Result.ofBoolResult` / `Result.ofBoolResult` 的定义

English:
definition Result.ofBoolResult
  signature: {p : Q(Prop)} {b : Bool} (prf : BoolResult p b)
  body: Result'.isBool b prf

中文:
定义 Result.of布尔Result
  签名: {p : Q(命题)} {b : 布尔值} (prf : 布尔Result p b)
  定义体: Result'.isBool b prf

Depends on / 依赖: Result, isBool
-/
def Result.ofBoolResult {p : Q(Prop)} {b : Bool} (prf : BoolResult p b) : Result q(Prop) :=
  Result'.isBool b prf

/--
Definition of `Result.eqTrans` / `Result.eqTrans` 的定义

English:
definition Result.eqTrans
  signature: {α : Q(Type u)} {a b : Q($α)} (eq : Q($a = $b))
  body: a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q($b) := proof
    Result.isTrue (x := a) q($eq ▸ $proof)
  | .isBool false proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q(¬ $b) := proof
    Result.isFalse (x := a) q($eq ▸ $proof)
  | .isNat inst lit proof => Result.isNat inst lit q($eq ▸ $proof)
  | .isNegNat inst lit proof => Result.isNegNat inst lit q($eq ▸ $proof)
  | .isNNRat inst q n d proof => Result.isNNRat inst q n d q($eq ▸ $proof)
  | .isNegNNRat inst q n d proof => Result.isNegNNRat inst q n d q($eq ▸ $proof)

中文:
定义 Result.eqTrans
  签名: {α : Q(类型u)} {a b : Q($α)} (eq : Q($a = $b))
  定义体: a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q($b) := proof
    Result.isTrue (x := a) q($eq ▸ $proof)
  | .isBool false proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q(¬ $b) := proof
    Result.isFalse (x := a) q($eq ▸ $proof)
  | .isNat inst lit proof => Result.isNat inst lit q($eq ▸ $proof)
  | .isNegNat inst lit proof => Result.isNegNat inst lit q($eq ▸ $proof)
  | .isNNRat inst q n d proof => Result.isNNRat inst q n d q($eq ▸ $proof)
  | .isNegNNRat inst q n d proof => Result.isNegNNRat inst q n d q($eq ▸ $proof)
-/
def Result.eqTrans {α : Q(Type u)} {a b : Q($α)} (eq : Q($a = $b)) : Result b -> Result a
  | .isBool true proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q($b) := proof
    Result.isTrue (x := a) q($eq ▸ $proof)
  | .isBool false proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q(¬ $b) := proof
    Result.isFalse (x := a) q($eq ▸ $proof)
  | .isNat inst lit proof => Result.isNat inst lit q($eq ▸ $proof)
  | .isNegNat inst lit proof => Result.isNegNat inst lit q($eq ▸ $proof)
  | .isNNRat inst q n d proof => Result.isNNRat inst q n d q($eq ▸ $proof)
  | .isNegNNRat inst q n d proof => Result.isNegNNRat inst q n d q($eq ▸ $proof)

end

end Meta.NormNum

end Mathlib
