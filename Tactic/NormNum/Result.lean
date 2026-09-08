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
/-
**Mathlib.Meta.NormNum.instAddMonoidWithOne'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Meta.NormNum`。
形式化陈述：instAddMonoidWithOne' {α : Type u} [Semiring α] : AddMonoidWithOne α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shortcut (non)instance for `AddMonoidWithOne α`
from `Semiring α` to shrink generated proofs.
-/
def instAddMonoidWithOne' {α : Type u} [Semiring α] : AddMonoidWithOne α := inferInstance

/-- A shortcut (non)instance for `AddMonoidWithOne α` from `Ring α` to shrink generated proofs. -/
@[instance_reducible]
/-
**Mathlib.Meta.NormNum.instAddMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.M
eta.NormNum`。
形式化陈述：instAddMonoidWithOne {α : Type u} [Ring α] : AddMonoidWithOne α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shortcut (non)instance for `AddMonoidWithOne α` from `Ring α` to shrink genera
ted proofs.
-/
def instAddMonoidWithOne {α : Type u} [Ring α] : AddMonoidWithOne α := inferInstance

/-- A shortcut (non)instance for `Nat.AtLeastTwo (n + 2)` to shrink generated proofs. -/
/-
**Mathlib.Meta.NormNum.instAtLeastTwo** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：instAtLeastTwo (n : Nat) : Nat.AtLeastTwo (n + 2)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
A shortcut (non)instance for `Nat.AtLeastTwo (n + 2)` to shrink generated proofs
.
-/
lemma instAtLeastTwo (n : ℕ) : Nat.AtLeastTwo (n + 2) := inferInstance

/-- Helper function to synthesize a typed `AddMonoidWithOne α` expression. -/
meta def inferAddMonoidWithOne (α : Q(Type u)) : MetaM Q(AddMonoidWithOne $α) :=
  return ← synthInstanceQ q(AddMonoidWithOne $α) <|>
    throwError "not an AddMonoidWithOne"

/-- Helper function to synthesize a typed `Semiring α` expression. -/
meta def inferSemiring (α : Q(Type u)) : MetaM Q(Semiring $α) :=
  return ← synthInstanceQ q(Semiring $α) <|> throwError "not a semiring"

/-- Helper function to synthesize a typed `Ring α` expression. -/
meta def inferRing (α : Q(Type u)) : MetaM Q(Ring $α) :=
  return ← synthInstanceQ q(Ring $α) <|> throwError "not a ring"

/--
Represent an integer as a "raw" typed expression.

This uses `.lit (.natVal n)` internally to represent a natural number,
rather than the preferred `OfNat.ofNat` form.
We use this internally to avoid unnecessary typeclass searches.

This function is the inverse of `Expr.intLit!`.
-/
meta def mkRawIntLit (n : ℤ) : Q(ℤ) :=
  let lit : Q(ℕ) := mkRawNatLit n.natAbs
  if 0 ≤ n then q(.ofNat $lit) else q(.negOfNat $lit)

/--
Represent an integer as a "raw" typed expression.

This `.lit (.natVal n)` internally to represent a natural number,
rather than the preferred `OfNat.ofNat` form.
We use this internally to avoid unnecessary typeclass searches.
-/
meta def mkRawRatLit (q : ℚ) : Q(ℚ) :=
  let nlit : Q(ℤ) := mkRawIntLit q.num
  let dlit : Q(ℕ) := mkRawNatLit q.den
  q(mkRat $nlit $dlit)

/-- Extract the raw natlit representing the absolute value of a raw integer literal
(of the type produced by `Mathlib.Meta.NormNum.mkRawIntLit`) along with an equality proof. -/
meta def rawIntLitNatAbs (n : Q(ℤ)) : (m : Q(ℕ)) × Q(Int.natAbs $n = $m) :=
  if n.isAppOfArity ``Int.ofNat 1 then
    have m : Q(ℕ) := n.appArg!
    ⟨m, show Q(Int.natAbs (Int.ofNat $m) = $m) from q(Int.natAbs_natCast $m)⟩
  else if n.isAppOfArity ``Int.negOfNat 1 then
    have m : Q(ℕ) := n.appArg!
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
meta def mkOfNat (α : Q(Type u)) (_sα : Q(AddMonoidWithOne $α)) (lit : Q(ℕ)) :
    MetaM ((a' : Q($α)) × Q($lit = $a')) := do
  if α.isConstOf ``Nat then
    let a' : Q(ℕ) := q(OfNat.ofNat $lit : ℕ)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else if α.isConstOf ``Int then
    let a' : Q(ℤ) := q(OfNat.ofNat $lit : ℤ)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else if α.isConstOf ``Rat then
    let a' : Q(ℚ) := q(OfNat.ofNat $lit : ℚ)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else
    let some n := lit.rawNatLit? | failure
    match n with
    | 0 => pure ⟨q(0 : $α), (q(Nat.cast_zero (R := $α)) : Expr)⟩
    | 1 => pure ⟨q(1 : $α), (q(Nat.cast_one (R := $α)) : Expr)⟩
    | k+2 =>
      let k : Q(ℕ) := mkRawNatLit k
      let _x : Q(Nat.AtLeastTwo $lit) :=
        (q(instAtLeastTwo $k) : Expr)
      let a' : Q($α) := q(OfNat.ofNat $lit)
      pure ⟨a', (q(Eq.refl $a') : Expr)⟩

/-- Assert that an element of a semiring is equal to the coercion of some natural number. -/
/-
**Mathlib.Meta.NormNum.IsNat** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：{α : Type u} → [AddMonoidWithOne α] → α → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assert that an element of a semiring is equal to the coercion of some natural nu
mber.
-/
structure IsNat {α : Type u} [AddMonoidWithOne α] (a : α) (n : ℕ) : Prop where
  /-- The element is equal to the coercion of the natural number. -/
  out : a = n
/-
**Mathlib.Meta.NormNum.IsNat.raw_refl** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsNat`。
形式化陈述：∀ (n : ℕ), Mathlib.Meta.NormNum.IsNat n n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsNat.raw_refl (n : ℕ) : IsNat n n := ⟨rfl⟩

/--
A "raw nat cast" is an expression of the form `(Nat.rawCast lit : α)` where `lit` is a raw
natural number literal. These expressions are used by tactics like `ring` to decrease the number
of typeclass arguments required in each use of a number literal at type `α`.
-/
/-
**Mathlib.Meta.NormNum._root_.Nat.rawCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Met
a.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "raw nat cast" is an expression of the form `(Nat.rawCast lit : α)` where `lit
` is a raw
natural number literal. These expressions are used by tactics like `ring` to dec
rease the number
of typeclass arguments required in each use of a number literal at type `α`.
-/
@[simp] def _root_.Nat.rawCast {α : Type u} [AddMonoidWithOne α] (n : ℕ) : α := n
/-
**Mathlib.Meta.NormNum.IsNat.to_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.NormN
um.IsNat`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] {n : ℕ} {a a' : α}, Mathlib.Met
a.NormNum.IsNat a n → ↑n = a' → a = a'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "raw nat cast" is an expression of the form `(Nat.rawCast lit : α)` where `lit
` is a raw
natural number literal. These expressions are used by tactics like `ring` to dec
rease the number
of typeclass arguments required in each use of a number literal at type `α`.
-/
theorem IsNat.to_eq {α : Type u} [AddMonoidWithOne α] {n} : {a a' : α} → IsNat a n → n = a' → a = a'
  | _, _, ⟨rfl⟩, rfl => rfl
/-
**Mathlib.Meta.NormNum.IsNat.to_raw_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum.IsNat`。
形式化陈述：∀ {α : Type u} {a : α} {n : ℕ} [inst : AddMonoidWithOne α], Mathlib.Meta.N
ormNum.IsNat a n → a = n.rawCast
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsNat.to_raw_eq {a : α} {n : ℕ} [AddMonoidWithOne α] : IsNat (a : α) n → a = n.rawCast
  | ⟨e⟩ => e
/-
**Mathlib.Meta.NormNum.IsNat.of_raw** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num.IsNat`。
形式化陈述：∀ (α : Type u_1) [inst : AddMonoidWithOne α] (n : ℕ), Mathlib.Meta.NormNum
.IsNat n.rawCast n
参数：α : Type u_1；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsNat.of_raw (α) [AddMonoidWithOne α] (n : ℕ) : IsNat (n.rawCast : α) n := ⟨rfl⟩

@[elab_as_elim]
/-
**Mathlib.Meta.NormNum.isNat.natElim** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum.isNat`。
形式化陈述：∀ {p : ℕ → Prop} {n n' : ℕ}, Mathlib.Meta.NormNum.IsNat n n' → p n' → p n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNat.natElim {p : ℕ → Prop} : {n : ℕ} → {n' : ℕ} → IsNat n n' → p n' → p n
  | _, _, ⟨rfl⟩, h => h

/-- Assert that an element of a ring is equal to the coercion of some integer. -/
/-
**Mathlib.Meta.NormNum.IsInt** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：{α : Type u} → [Ring α] → α → ℤ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assert that an element of a ring is equal to the coercion of some integer.
-/
structure IsInt [Ring α] (a : α) (n : ℤ) : Prop where
  /-- The element is equal to the coercion of the integer. -/
  out : a = n

/--
A "raw int cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural number literal

(That is, we only actually use this function for negative integers.) This representation is used by
tactics like `ring` to decrease the number of typeclass arguments required in each use of a number
literal at type `α`.
-/
/-
**Mathlib.Meta.NormNum._root_.Int.rawCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Met
a.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "raw int cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural nu
mber literal

(That is, we only actually use this function for negative integers.) This repres
entation is used by
tactics like `ring` to decrease the number of typeclass arguments required in ea
ch use of a number
literal at type `α`.
-/
@[simp] def _root_.Int.rawCast [Ring α] (n : ℤ) : α := n
/-
**Mathlib.Meta.NormNum.IsInt.to_isNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsInt`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.I
sInt a (Int.ofNat n) → Mathlib.Meta.NormNum.IsNat a n
参数：Int.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A "raw int cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural nu
mber literal

(That is, we only actually use this function for negative integers.) This repres
entation is used by
tactics like `ring` to decrease the number of typeclass arguments required in ea
ch use of a number
literal at type `α`.
-/
theorem IsInt.to_isNat {α} [Ring α] : ∀ {a : α} {n}, IsInt a (.ofNat n) → IsNat a n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.IsNat.to_isInt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsNat`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.I
sNat a n → Mathlib.Meta.NormNum.IsInt a (Int.ofNat n)
参数：Int.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNat.to_isInt {α} [Ring α] : ∀ {a : α} {n}, IsNat a n → IsInt a (.ofNat n)
  | _, _, ⟨rfl⟩ => ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.IsInt.to_raw_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum.IsInt`。
形式化陈述：∀ {α : Type u} {a : α} {n : ℤ} [inst : Ring α], Mathlib.Meta.NormNum.IsInt
 a n → a = n.rawCast
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsInt.to_raw_eq {a : α} {n : ℤ} [Ring α] : IsInt (a : α) n → a = n.rawCast
  | ⟨e⟩ => e
/-
**Mathlib.Meta.NormNum.IsInt.of_raw** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num.IsInt`。
形式化陈述：∀ (α : Type u_1) [inst : Ring α] (n : ℤ), Mathlib.Meta.NormNum.IsInt n.raw
Cast n
参数：α : Type u_1；n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsInt.of_raw (α) [Ring α] (n : ℤ) : IsInt (n.rawCast : α) n := ⟨rfl⟩
/-
**Mathlib.Meta.NormNum.IsInt.neg_to_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum.IsInt`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.
IsInt a (Int.negOfNat n) → ↑n = a' → a = -a'
参数：Int.negOfNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsInt.neg_to_eq {α} [Ring α] {n} :
    {a a' : α} → IsInt a (.negOfNat n) → n = a' → a = -a'
  | _, _, ⟨rfl⟩, rfl => by simp [Int.negOfNat_eq, Int.cast_neg]
/-
**Mathlib.Meta.NormNum.IsInt.nonneg_to_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Met
a.NormNum.IsInt`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.
IsInt a (Int.ofNat n) → ↑n = a' → a = a'
参数：Int.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
-/
theorem IsInt.nonneg_to_eq {α} [Ring α] {n}
    {a a' : α} (h : IsInt a (.ofNat n)) (e : n = a') : a = a' := h.to_isNat.to_eq e

/--
Assert that an element of a ring is equal to `num / denom`
(and `denom` is invertible so that this makes sense).
We will usually also have `num` and `denom` coprime,
although this is not part of the definition.
-/
/-
**Mathlib.Meta.NormNum.IsRat** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：{α : Type u} → [Ring α] → α → ℤ → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assert that an element of a ring is equal to `num / denom`
(and `denom` is invertible so that this makes sense).
We will usually also have `num` and `denom` coprime,
although this is not part of the definition.
-/
inductive IsRat [Ring α] (a : α) (num : ℤ) (denom : ℕ) : Prop
  | mk (inv : Invertible (denom : α)) (eq : a = num * ⅟(denom : α))

/--
Assert that an element of a semiring is equal to `num / denom`
(and `denom` is invertible so that this makes sense).
We will usually also have `num` and `denom` coprime,
although this is not part of the definition.
-/
/-
**Mathlib.Meta.NormNum.IsNNRat** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：{α : Type u} → [Semiring α] → α → ℕ → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assert that an element of a semiring is equal to `num / denom`
(and `denom` is invertible so that this makes sense).
We will usually also have `num` and `denom` coprime,
although this is not part of the definition.
-/
inductive IsNNRat [Semiring α] (a : α) (num : ℕ) (denom : ℕ) : Prop
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
/-
**Mathlib.Meta.NormNum._root_.NNRat.rawCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.M
eta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "raw nnrat cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(NNRat.rawCast n d : α)` where `n` is a raw nat literal, `d` is a raw nat lit
eral, and `d` is not
  `1` or `0`.

This representation is used by tactics like `ring` to decrease the number of typ
eclass arguments
required in each use of a number literal at type `α`.
-/
def _root_.NNRat.rawCast [DivisionSemiring α] (n : ℕ) (d : ℕ) : α := n / d

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
/-
**Mathlib.Meta.NormNum._root_.Rat.rawCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Met
a.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "raw rat cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural nu
mber literal
* `(NNRat.rawCast n d : α)` where `n` is a raw nat literal, `d` is a raw nat lit
eral, and `d` is not
  `1` or `0`.
* `(Rat.rawCast (Int.negOfNat n) d : α)` where `n` is a raw nat literal,
  `d` is a raw nat literal, `n` is not `0`, and `d` is not `1` or `0`.

This representation is used by tactics like `ring` to decrease the number of typ
eclass arguments
required in each use of a number literal at type `α`.
-/
def _root_.Rat.rawCast [DivisionRing α] (n : ℤ) (d : ℕ) : α := n / d
/-
**Mathlib.Meta.NormNum.IsNNRat.to_isNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum.IsNNRat`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] {a : α} {n : ℕ},   Mathlib.Meta.NormN
um.IsNNRat a n 1 → Mathlib.Meta.NormNum.IsNat a n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `invOf_one'`：invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 
1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNNRat.to_isNat {α} [Semiring α] : ∀ {a : α} {n}, IsNNRat a (n) (nat_lit 1) → IsNat a n
  | _, num, ⟨inv, rfl⟩ => have := @invertibleOne α _; ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.IsRat.to_isNNRat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum.IsRat`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {a : α} {n d : ℕ},   Mathlib.Meta.NormNum
.IsRat a (Int.ofNat n) d → Mathlib.Meta.NormNum.IsNNRat a n d
参数：Int.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRat.to_isNNRat {α} [Ring α] : ∀ {a : α} {n d}, IsRat a (.ofNat n) (d) → IsNNRat a n d
  | _, _, _, ⟨inv, rfl⟩ => ⟨inv, by simp⟩
/-
**Mathlib.Meta.NormNum.IsNat.to_isNNRat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum.IsNat`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] {a : α} {n : ℕ},   Mathlib.Meta.NormN
um.IsNat a n → Mathlib.Meta.NormNum.IsNNRat a n 1
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
theorem IsNat.to_isNNRat {α} [Semiring α] : ∀ {a : α} {n}, IsNat a n → IsNNRat a (n) (nat_lit 1)
  | _, _, ⟨rfl⟩ => ⟨⟨1, by simp, by simp⟩, by simp⟩
/-
**Mathlib.Meta.NormNum.IsNNRat.to_isRat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum.IsNNRat`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {a : α} {n d : ℕ},   Mathlib.Meta.NormNum
.IsNNRat a n d → Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d
参数：Int.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNNRat.to_isRat {α} [Ring α] : ∀ {a : α} {n d}, IsNNRat a n d → IsRat a (.ofNat n) d
  | _, _, _, ⟨inv, rfl⟩ => ⟨inv, by simp⟩
/-
**Mathlib.Meta.NormNum.IsRat.to_isInt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsRat`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {a : α} {n : ℤ}, Mathlib.Meta.NormNum.IsR
at a n 1 → Mathlib.Meta.NormNum.IsInt a n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `invOf_one'`：invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 
1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRat.to_isInt {α} [Ring α] : ∀ {a : α} {n}, IsRat a n (nat_lit 1) → IsInt a n
  | _, _, ⟨inv, rfl⟩ => have := @invertibleOne α _; ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.IsInt.to_isRat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsInt`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] {a : α} {n : ℤ}, Mathlib.Meta.NormNum.IsI
nt a n → Mathlib.Meta.NormNum.IsRat a n 1
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
theorem IsInt.to_isRat {α} [Ring α] : ∀ {a : α} {n}, IsInt a n → IsRat a n (nat_lit 1)
  | _, _, ⟨rfl⟩ => ⟨⟨1, by simp, by simp⟩, by simp⟩
/-
**Mathlib.Meta.NormNum.IsNNRat.to_raw_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum.IsNNRat`。
形式化陈述：∀ {α : Type u} {n d : ℕ} [inst : DivisionSemiring α] {a : α}, Mathlib.Meta
.NormNum.IsNNRat a n d → a = NNRat.rawCast n d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNNRat.to_raw_eq {n d : ℕ} [DivisionSemiring α] :
    ∀ {a}, IsNNRat (a : α) n d → a = NNRat.rawCast n d
  | _, ⟨inv, rfl⟩ => by simp [div_eq_mul_inv]
/-
**Mathlib.Meta.NormNum.IsRat.to_raw_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum.IsRat`。
形式化陈述：∀ {α : Type u} {n : ℤ} {d : ℕ} [inst : DivisionRing α] {a : α}, Mathlib.Me
ta.NormNum.IsRat a n d → a = Rat.rawCast n d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRat.to_raw_eq {n : ℤ} {d : ℕ} [DivisionRing α] :
    ∀ {a}, IsRat (a : α) n d → a = Rat.rawCast n d
  | _, ⟨inv, rfl⟩ => by simp [div_eq_mul_inv]
/-
**Mathlib.Meta.NormNum.IsRat.neg_to_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum.IsRat`。
形式化陈述：∀ {α : Type u_1} [inst : DivisionRing α] {n d : ℕ} {a n' d' : α},   Mathli
b.Meta.NormNum.IsRat a (Int.negOfNat n) d → ↑n = n' → ↑d = d' → a = -(n' / d')
参数：Int.negOfNat n；n' / d'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRat.neg_to_eq {α} [DivisionRing α] {n d} :
    {a n' d' : α} → IsRat a (.negOfNat n) d → n = n' → d = d' → a = -(n' / d')
  | _, _, _, ⟨_, rfl⟩, rfl, rfl => by simp [div_eq_mul_inv]
/-
**Mathlib.Meta.NormNum.IsNNRat.to_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum.IsNNRat`。
形式化陈述：∀ {α : Type u_1} [inst : DivisionSemiring α] {n d : ℕ} {a n' d' : α},   Ma
thlib.Meta.NormNum.IsNNRat a n d → ↑n = n' → ↑d = d' → a = n' / d'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNNRat.to_eq {α} [DivisionSemiring α] {n d} :
    {a n' d' : α} → IsNNRat a n d → n = n' → d = d' → a = n' / d'
  | _, _, _, ⟨_, rfl⟩, rfl, rfl => by simp [div_eq_mul_inv]
/-
**Mathlib.Meta.NormNum.IsNNRat.of_raw** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsNNRat`。
形式化陈述：∀ (α : Type u_1) [inst : DivisionSemiring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.M
eta.NormNum.IsNNRat (NNRat.rawCast n d) n d
参数：α : Type u_1；n d : ℕ；NNRat.rawCast n d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNNRat.of_raw (α) [DivisionSemiring α] (n : ℕ) (d : ℕ)
    (h : (d : α) ≠ 0) : IsNNRat (NNRat.rawCast n d : α) n d :=
  have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩
/-
**Mathlib.Meta.NormNum.IsRat.of_raw** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num.IsRat`。
形式化陈述：∀ (α : Type u_1) [inst : DivisionRing α] (n : ℤ) (d : ℕ), ↑d ≠ 0 → Mathlib
.Meta.NormNum.IsRat (Rat.rawCast n d) n d
参数：α : Type u_1；n : ℤ；d : ℕ；Rat.rawCast n d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRat.of_raw (α) [DivisionRing α] (n : ℤ) (d : ℕ)
    (h : (d : α) ≠ 0) : IsRat (Rat.rawCast n d : α) n d :=
  have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩
/-
**Mathlib.Meta.NormNum.IsNNRat.den_nz** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum.IsNNRat`。
形式化陈述：∀ {α : Type u_1} [inst : DivisionSemiring α] {a : α} {n d : ℕ}, Mathlib.Me
ta.NormNum.IsNNRat a n d → ↑d ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem IsNNRat.den_nz {α} [DivisionSemiring α] {a n d} : IsNNRat (a : α) n d → (d : α) ≠ 0
  | ⟨_, _⟩ => Invertible.ne_zero (d : α)
/-
**Mathlib.Meta.NormNum.IsRat.den_nz** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Norm
Num.IsRat`。
形式化陈述：∀ {α : Type u_1} [inst : DivisionRing α] {a : α} {n : ℤ} {d : ℕ}, Mathlib.
Meta.NormNum.IsRat a n d → ↑d ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem IsRat.den_nz {α} [DivisionRing α] {a n d} : IsRat (a : α) n d → (d : α) ≠ 0
  | ⟨_, _⟩ => Invertible.ne_zero (d : α)

meta section

/-- The result of `norm_num` running on an expression `x` of type `α`.
Untyped version of `Result`. -/
/-
**Mathlib.Meta.NormNum.Result'** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.NormNum
`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of `norm_num` running on an expression `x` of type `α`.
Untyped version of `Result`.
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

/-- The result of `norm_num` running on an expression `x` of type `α`. -/
/-
**Mathlib.Meta.NormNum.Result** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：{u : Level} → {α : Q(Type u)} → Q(«$α») → Type
参数：Type u；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result of `norm_num` running on an expression `x` of type `α`.
-/
@[nolint unusedArguments] def Result {α : Q(Type u)} (x : Q($α)) := Result'

-- The new behaviour of `inferInstanceAs` from leanprover/lean4#12897 needs to be updated,
-- to ensure that if we are in a `meta` section then the auxiliary definitions are also `meta`.
-- Fixed in https://github.com/leanprover/lean4/pull/13043
/-
**Mathlib.Meta.NormNum.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Q(Type u)} {x : Q($α)} : Inhabited (Result x) := inferInstanceAs (Inhabited Result')

/-- The result is `proof : x`, where `x` is a (true) proposition. -/
/-
**Mathlib.Meta.NormNum.Result.isTrue** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Nor
mNum.Result`。
形式化陈述：{x : Q(Prop)} → Q(«$x») → Mathlib.Meta.NormNum.Result q(«$x»)
参数：Prop；«$x»；«$x»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result is `proof : x`, where `x` is a (true) proposition.
-/
@[match_pattern, inline] def Result.isTrue {x : Q(Prop)} :
    ∀ (proof : Q($x)), Result q($x) := Result'.isBool true

/-- The result is `proof : ¬x`, where `x` is a (false) proposition. -/
/-
**Mathlib.Meta.NormNum.Result.isFalse** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum.Result`。
形式化陈述：{x : Q(Prop)} → Q(¬«$x») → Mathlib.Meta.NormNum.Result q(«$x»)
参数：Prop；¬«$x»；«$x»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result is `proof : ¬x`, where `x` is a (false) proposition.
-/
@[match_pattern, inline] def Result.isFalse {x : Q(Prop)} :
    ∀ (proof : Q(¬$x)), Result q($x) := Result'.isBool false

/-- The result is `lit : ℕ` (a raw nat literal) and `proof : isNat x lit`. -/
/-
**Mathlib.Meta.NormNum.Result.isNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {x : Q(«$α»)} →       (inst : autoPa
ram Q(AddMonoidWithOne «$α») Mathlib.Meta.NormNum.Result.isNat._auto_1) →       
  (lit : Q(ℕ)) → Q(Mathlib.Meta.NormNum.IsNat «$x» «$lit») → Mathlib.Meta.NormNu
m.Result x
参数：Type u；«$α»；inst : autoParam Q(AddMonoidWithOne «$α») Mathlib.Meta.NormNum.Re
sult.isNat._auto_1；lit : Q(ℕ)；Mathlib.Meta.NormNum.IsNat «$x» «$lit»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result is `lit : ℕ` (a raw nat literal) and `proof : isNat x lit`.
-/
@[match_pattern, inline] def Result.isNat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(AddMonoidWithOne $α) := by assumption) (lit : Q(ℕ)) (proof : Q(IsNat $x $lit)),
      Result x := Result'.isNat

/-- The result is `-lit` where `lit` is a raw nat literal
and `proof : isInt x (.negOfNat lit)`. -/
/-
**Mathlib.Meta.NormNum.Result.isNegNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {x : Q(«$α»)} →       (inst : autoPa
ram Q(Ring «$α») Mathlib.Meta.NormNum.Result.isNegNat._auto_1) →         (lit : 
Q(ℕ)) → Q(Mathlib.Meta.NormNum.IsInt «$x» (Int.negOfNat «$lit»)) → Mathlib.Meta.
NormNum.Result x
参数：Type u；«$α»；inst : autoParam Q(Ring «$α») Mathlib.Meta.NormNum.Result.isNegNa
t._auto_1；lit : Q(ℕ)；Mathlib.Meta.NormNum.IsInt «$x» (Int.negOfNat «$lit»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result is `-lit` where `lit` is a raw nat literal
and `proof : isInt x (.negOfNat lit)`.
-/
@[match_pattern, inline] def Result.isNegNat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(Ring $α) := by assumption) (lit : Q(ℕ)) (proof : Q(IsInt $x (.negOfNat $lit))),
      Result x := Result'.isNegNat

/-- The result is `proof : IsNNRat x n d`,
where `n` a raw nat literal, `d` is a raw nat literal (not 0 or 1),
`n` and `d` are coprime, and `q` is the value of `n / d`. -/
/-
**Mathlib.Meta.NormNum.Result.isNNRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {x : Q(«$α»)} →       (inst : autoPa
ram Q(DivisionSemiring «$α») Mathlib.Meta.NormNum.Result.isNNRat._auto_1) →     
    ℚ → (n d : Q(ℕ)) → Q(Mathlib.Meta.NormNum.IsNNRat «$x» «$n» «$d») → Mathlib.
Meta.NormNum.Result x
参数：Type u；«$α»；inst : autoParam Q(DivisionSemiring «$α») Mathlib.Meta.NormNum.Re
sult.isNNRat._auto_1；n d : Q(ℕ)；Mathlib.Meta.NormNum.IsNNRat «$x» «$n» «$d»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result is `proof : IsNNRat x n d`,
where `n` a raw nat literal, `d` is a raw nat literal (not 0 or 1),
`n` and `d` are coprime, and `q` is the value of `n / d`.
-/
@[match_pattern, inline] def Result.isNNRat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(DivisionSemiring $α) := by assumption) (q : Rat) (n : Q(ℕ)) (d : Q(ℕ))
      (proof : Q(IsNNRat $x $n $d)), Result x := Result'.isNNRat

/-- The result is `proof : IsRat x n d`,
where `n` is `.negOfNat lit` with `lit` a raw nat literal,
`d` is a raw nat literal (not 0 or 1),
`n` and `d` are coprime, and `q` is the value of `n / d`. -/
/-
**Mathlib.Meta.NormNum.Result.isNegNNRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta
.NormNum.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {x : Q(«$α»)} →       (inst : autoPa
ram Q(DivisionRing «$α») Mathlib.Meta.NormNum.Result.isNegNNRat._auto_1) →      
   ℚ → (n d : Q(ℕ)) → Q(Mathlib.Meta.NormNum.IsRat «$x» (Int.negOfNat «$n») «$d»
) → Mathlib.Meta.NormNum.Result x
参数：Type u；«$α»；inst : autoParam Q(DivisionRing «$α») Mathlib.Meta.NormNum.Result
.isNegNNRat._auto_1；n d : Q(ℕ)；Mathlib.Meta.NormNum.IsRat «$x» (Int.negOfNat «$n
») «$d»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The result is `proof : IsRat x n d`,
where `n` is `.negOfNat lit` with `lit` a raw nat literal,
`d` is a raw nat literal (not 0 or 1),
`n` and `d` are coprime, and `q` is the value of `n / d`.
-/
@[match_pattern, inline] def Result.isNegNNRat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(DivisionRing $α) := by assumption) (q : Rat) (n : Q(ℕ)) (d : Q(ℕ))
      (proof : Q(IsRat $x (.negOfNat $n) $d)), Result x := Result'.isNegNNRat

end

/-- The result is `z : ℤ` and `proof : isNat x z`. -/
-- Note the independent arguments `z : Q(ℤ)` and `n : ℤ`.
-- We ensure these are "the same" when calling.
/-
**Mathlib.Meta.NormNum.Result.isInt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {x : Q(«$α»)} →       (inst : autoPa
ram Q(Ring «$α») Mathlib.Meta.NormNum.Result.isInt._auto_1) →         (z : Q(ℤ))
 → ℤ → Q(Mathlib.Meta.NormNum.IsInt «$x» «$z») → Mathlib.Meta.NormNum.Result x
参数：Type u；«$α»；inst : autoParam Q(Ring «$α») Mathlib.Meta.NormNum.Result.isInt._
auto_1；z : Q(ℤ)；Mathlib.Meta.NormNum.IsInt «$x» «$z»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Result.isInt {α : Q(Type u)} {x : Q($α)} (inst : Q(Ring $α) := by assumption)
    (z : Q(ℤ)) (n : ℤ) (proof : Q(IsInt $x $z)) : Result x :=
  have lit : Q(ℕ) := z.appArg!
  if 0 ≤ n then
    let proof : Q(IsInt $x (.ofNat $lit)) := proof
    .isNat q(instAddMonoidWithOne) lit q(IsInt.to_isNat $proof)
  else
    .isNegNat inst lit proof

/-- The result is `q : NNRat` and `proof : isNNRat x q`. -/
-- Note the independent arguments `q : Q(ℚ)` and `n : ℚ`.
-- We ensure these are "the same" when calling.
/-
**Mathlib.Meta.NormNum.Result.isNNRat'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {x : Q(«$α»)} →       (inst : autoPa
ram Q(DivisionSemiring «$α») Mathlib.Meta.NormNum.Result.isNNRat'._auto_1) →    
     ℚ → (n d : Q(ℕ)) → Q(Mathlib.Meta.NormNum.IsNNRat «$x» «$n» «$d») → Mathlib
.Meta.NormNum.Result x
参数：Type u；«$α»；inst : autoParam Q(DivisionSemiring «$α») Mathlib.Meta.NormNum.Re
sult.isNNRat'._auto_1；n d : Q(ℕ)；Mathlib.Meta.NormNum.IsNNRat «$x» «$n» «$d»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Result.isNNRat' {α : Q(Type u)} {x : Q($α)} (inst : Q(DivisionSemiring $α) := by assumption)
    (q : Rat) (n : Q(ℕ)) (d : Q(ℕ)) (proof : Q(IsNNRat $x $n $d)) : Result x :=
  if q.den = 1 then
    haveI : nat_lit 1 =Q $d := ⟨⟩
    .isNat q(instAddMonoidWithOne') n q(IsNNRat.to_isNat $proof)
  else
    .isNNRat inst q n d proof

/-- The result is `q : ℚ` and `proof : isRat x q`. -/
-- Note the independent arguments `q : Q(ℚ)` and `n : ℚ`.
-- We ensure these are "the same" when calling.
/-
**Mathlib.Meta.NormNum.Result.isRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {x : Q(«$α»)} →       (inst : autoPa
ram Q(DivisionRing «$α») Mathlib.Meta.NormNum.Result.isRat._auto_1) →         ℚ 
→ (n : Q(ℤ)) → (d : Q(ℕ)) → Q(Mathlib.Meta.NormNum.IsRat «$x» «$n» «$d») → Mathl
ib.Meta.NormNum.Result x
参数：Type u；«$α»；inst : autoParam Q(DivisionRing «$α») Mathlib.Meta.NormNum.Result
.isRat._auto_1；n : Q(ℤ)；d : Q(ℕ)；Mathlib.Meta.NormNum.IsRat «$x» «$n» «$d»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Result.isRat {α : Q(Type u)} {x : Q($α)} (inst : Q(DivisionRing $α) := by assumption)
    (q : ℚ) (n : Q(ℤ)) (d : Q(ℕ)) (proof : Q(IsRat $x $n $d)) : Result x :=
  have lit : Q(ℕ) := n.appArg!
  if q.den = 1 then
    have proof : Q(IsRat $x $n (nat_lit 1)) := proof
    .isInt q(DivisionRing.toRing) n q.num q(IsRat.to_isInt $proof)
  else if 0 ≤ q then
    let proof : Q(IsRat $x (.ofNat $lit) $d) := proof
    .isNNRat q(DivisionRing.toDivisionSemiring) q lit d q(IsRat.to_isNNRat $proof)
  else
    .isNegNNRat inst q lit d proof
/-
**Mathlib.Meta.NormNum.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Meta.NormNum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Q(Type u)} {x : Q($α)} : ToMessageData (Result x) where
  toMessageData
  | .isBool true proof => m!"isTrue ({proof})"
  | .isBool false proof => m!"isFalse ({proof})"
  | .isNat _ lit proof => m!"isNat {lit} ({proof})"
  | .isNegNat _ lit proof => m!"isNegNat {lit} ({proof})"
  | .isNNRat _ q _ _ proof => m!"isNNRat {q} ({proof})"
  | .isNegNNRat _ q _ _ proof => m!"isNegNNRat {q} ({proof})"

/-- Returns the rational number that is the result of `norm_num` evaluation. -/
/-
**Mathlib.Meta.NormNum.Result.toRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num.Result`。
形式化陈述：{u : Level} → {α : Q(Type u)} → {e : Q(«$α»)} → Mathlib.Meta.NormNum.Resul
t e → Option ℚ
参数：Type u；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the rational number that is the result of `norm_num` evaluation.
-/
def Result.toRat {α : Q(Type u)} {e : Q($α)} : Result e → Option Rat
  | .isBool .. => none
  | .isNat _ lit _ => some lit.natLit!
  | .isNegNat _ lit _ => some (-lit.natLit!)
  | .isNNRat _ q .. => some q
  | .isNegNNRat _ q .. => some q

/-- Returns the rational number that is the result of `norm_num` evaluation, along with a proof
that the denominator is nonzero in the `isRat` case. -/
/-
**Mathlib.Meta.NormNum.Result.toRatNZ** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum.Result`。
形式化陈述：{u : Level} → {α : Q(Type u)} → {e : Q(«$α»)} → Mathlib.Meta.NormNum.Resul
t e → Option (ℚ × Option Expr)
参数：Type u；«$α»；ℚ × Option Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the rational number that is the result of `norm_num` evaluation, along w
ith a proof
that the denominator is nonzero in the `isRat` case.
-/
def Result.toRatNZ {α : Q(Type u)} {e : Q($α)} : Result e → Option (Rat × Option Expr)
  | .isBool .. => none
  | .isNat _ lit _ => some (lit.natLit!, none)
  | .isNegNat _ lit _ => some (-lit.natLit!, none)
  | .isNNRat _ q _ _ p => some (q, q(IsNNRat.den_nz $p))
  | .isNegNNRat _ q _ _ p => some (q, q(IsRat.den_nz $p))

/--
Extract from a `Result` the integer value (as both a term and an expression),
and the proof that the original expression is equal to this integer.
-/
/-
**Mathlib.Meta.NormNum.Result.toInt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {e : Q(«$α»)} →       (_i : autoPara
m Q(Ring «$α») Mathlib.Meta.NormNum.Result.toInt._auto_1) →         Mathlib.Meta
.NormNum.Result e → Option (ℤ × (lit : Q(ℤ)) × Q(Mathlib.Meta.NormNum.IsInt «$e»
 «$lit»))
参数：Type u；«$α»；_i : autoParam Q(Ring «$α») Mathlib.Meta.NormNum.Result.toInt._au
to_1；ℤ × (lit : Q(ℤ)) × Q(Mathlib.Meta.NormNum.IsInt «$e» «$lit»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract from a `Result` the integer value (as both a term and an expression),
and the proof that the original expression is equal to this integer.
-/
def Result.toInt {α : Q(Type u)} {e : Q($α)} (_i : Q(Ring $α) := by with_reducible assumption) :
    Result e → Option (ℤ × (lit : Q(ℤ)) × Q(IsInt $e $lit))
  | .isNat _ lit proof => do
    have proof : Q(@IsNat _ instAddMonoidWithOne $e $lit) := proof
    pure ⟨lit.natLit!, q(.ofNat $lit), q(($proof).to_isInt)⟩
  | .isNegNat _ lit proof => pure ⟨-lit.natLit!, q(.negOfNat $lit), proof⟩
  | _ => failure

/--
Extract from a `Result` the rational value (as both a term and an expression),
and the proof that the original expression is equal to this rational number.
-/
/-
**Mathlib.Meta.NormNum.Result.toNNRat'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {e : Q(«$α»)} →       (_i : autoPara
m Q(DivisionSemiring «$α») Mathlib.Meta.NormNum.Result.toNNRat'._auto_1) →      
   Mathlib.Meta.NormNum.Result e →           Option (ℚ × (n : Q(ℕ)) × (d : Q(ℕ))
 × Q(Mathlib.Meta.NormNum.IsNNRat «$e» «$n» «$d»))
参数：Type u；«$α»；_i : autoParam Q(DivisionSemiring «$α») Mathlib.Meta.NormNum.Resu
lt.toNNRat'._auto_1；ℚ × (n : Q(ℕ)) × (d : Q(ℕ)) × Q(Mathlib.Meta.NormNum.IsNNRat
 «$e» «$n» «$d»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract from a `Result` the rational value (as both a term and an expression),
and the proof that the original expression is equal to this rational number.
-/
def Result.toNNRat' {α : Q(Type u)} {e : Q($α)}
    (_i : Q(DivisionSemiring $α) := by with_reducible assumption) :
    Result e → Option (Rat × (n : Q(ℕ)) × (d : Q(ℕ)) × Q(IsNNRat $e $n $d))
  | .isNat _ lit proof =>
    have proof : Q(@IsNat _ instAddMonoidWithOne' $e $lit) := proof
    some ⟨lit.natLit!, q($lit), q(nat_lit 1), q(($proof).to_isNNRat)⟩
  | .isNNRat _ q n d proof => some ⟨q, n, d, proof⟩
  | _ => none

/--
Extract from a `Result` the rational value (as both a term and an expression),
and the proof that the original expression is equal to this rational number.
-/
/-
**Mathlib.Meta.NormNum.Result.toRat'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Nor
mNum.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {e : Q(«$α»)} →       (_i : autoPara
m Q(DivisionRing «$α») Mathlib.Meta.NormNum.Result.toRat'._auto_1) →         Mat
hlib.Meta.NormNum.Result e →           Option (ℚ × (n : Q(ℤ)) × (d : Q(ℕ)) × Q(M
athlib.Meta.NormNum.IsRat «$e» «$n» «$d»))
参数：Type u；«$α»；_i : autoParam Q(DivisionRing «$α») Mathlib.Meta.NormNum.Result.t
oRat'._auto_1；ℚ × (n : Q(ℤ)) × (d : Q(ℕ)) × Q(Mathlib.Meta.NormNum.IsRat «$e» «$
n» «$d»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract from a `Result` the rational value (as both a term and an expression),
and the proof that the original expression is equal to this rational number.
-/
def Result.toRat' {α : Q(Type u)} {e : Q($α)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) :
    Result e → Option (ℚ × (n : Q(ℤ)) × (d : Q(ℕ)) × Q(IsRat $e $n $d))
  | .isBool .. => none
  | .isNat _ lit proof =>
    have proof : Q(@IsNat _ instAddMonoidWithOne $e $lit) := proof
    some ⟨lit.natLit!, q(.ofNat $lit), q(nat_lit 1), q(($proof).to_isNNRat.to_isRat)⟩
  | .isNegNat _ lit proof =>
    have proof : Q(@IsInt _ DivisionRing.toRing $e (.negOfNat $lit)) := proof
    some ⟨-lit.natLit!, q(.negOfNat $lit), q(nat_lit 1),
      q(@IsInt.to_isRat _ DivisionRing.toRing _ _ $proof)⟩
  | .isNNRat inst q n d proof =>
    letI : $inst =Q DivisionRing.toDivisionSemiring := ⟨⟩
    some ⟨q, q(.ofNat $n), d, q(IsNNRat.to_isRat $proof)⟩
  | .isNegNNRat _ q n d proof => some ⟨q, q(.negOfNat $n), d, proof⟩

/--
Given a `NormNum.Result e` (which uses `IsNat`, `IsInt`, `IsRat` to express equality to a rational
numeral), converts it to an equality `e = Nat.rawCast n`, `e = Int.rawCast n`, or
`e = Rat.rawCast n d` to a raw cast expression, so it can be used for rewriting.
-/
/-
**Mathlib.Meta.NormNum.Result.toRawEq** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum.Result`。
形式化陈述：{u : Level} → {α : Q(Type u)} → {e : Q(«$α»)} → Mathlib.Meta.NormNum.Resul
t e → (e' : Q(«$α»)) × Q(«$e» = «$e'»)
参数：Type u；«$α»；e' : Q(«$α»)；«$e» = «$e'»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `NormNum.Result e` (which uses `IsNat`, `IsInt`, `IsRat` to express equa
lity to a rational
numeral), converts it to an equality `e = Nat.rawCast n`, `e = Int.rawCast n`, o
r
`e = Rat.rawCast n d` to a raw cast expression, so it can be used for rewriting.
-/
def Result.toRawEq {α : Q(Type u)} {e : Q($α)} : Result e → (e' : Q($α)) × Q($e = $e')
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
`Result.toRawEq` but providing an integer. Given a `NormNum.Result e` for something known to be an
integer (which uses `IsNat` or `IsInt` to express equality to an integer numeral), converts it to
an equality `e = Nat.rawCast n` or `e = Int.rawCast n` to a raw cast expression, so it can be used
for rewriting. Gives `none` if not an integer.
-/
/-
**Mathlib.Meta.NormNum.Result.toRawIntEq** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta
.NormNum.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} → {e : Q(«$α»)} → Mathlib.Meta.NormNum.Res
ult e → Option (ℤ × (e' : Q(«$α»)) × Q(«$e» = «$e'»))
参数：Type u；«$α»；ℤ × (e' : Q(«$α»)) × Q(«$e» = «$e'»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Result.toRawEq` but providing an integer. Given a `NormNum.Result e` for someth
ing known to be an
integer (which uses `IsNat` or `IsInt` to express equality to an integer numeral
), converts it to
an equality `e = Nat.rawCast n` or `e = Int.rawCast n` to a raw cast expression,
 so it can be used
for rewriting. Gives `none` if not an integer.
-/
def Result.toRawIntEq {α : Q(Type u)} {e : Q($α)} : Result e →
    Option (ℤ × (e' : Q($α)) × Q($e = $e'))
  | .isNat _ lit p => some ⟨lit.natLit!, q(Nat.rawCast $lit), q(IsNat.to_raw_eq $p)⟩
  | .isNegNat _ lit p => some ⟨-lit.natLit!, q(Int.rawCast (.negOfNat $lit)), q(IsInt.to_raw_eq $p)⟩
  | .isNNRat _ .. | .isNegNNRat _ .. | .isBool .. => none

/-- Constructs a `Result` out of a raw nat cast. Assumes `e` is a raw nat cast expression. -/
/-
**Mathlib.Meta.NormNum.Result.ofRawNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum.Result`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (e : Q(«$α»)) → Mathlib.Meta.NormNum.Resul
t e
参数：Type u；e : Q(«$α»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a `Result` out of a raw nat cast. Assumes `e` is a raw nat cast expre
ssion.
-/
def Result.ofRawNat {α : Q(Type u)} (e : Q($α)) : Result e := Id.run do
  let .app (.app _ (sα : Q(AddMonoidWithOne $α))) (lit : Q(ℕ)) := e | panic! "not a raw nat cast"
  .isNat sα lit (q(IsNat.of_raw $α $lit) : Expr)

/-- Constructs a `Result` out of a raw int cast.
Assumes `e` is a raw int cast expression denoting `n`. -/
/-
**Mathlib.Meta.NormNum.Result.ofRawInt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum.Result`。
形式化陈述：{u : Level} → {α : Q(Type u)} → ℤ → (e : Q(«$α»)) → Mathlib.Meta.NormNum.R
esult e
参数：Type u；e : Q(«$α»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a `Result` out of a raw int cast.
Assumes `e` is a raw int cast expression denoting `n`.
-/
def Result.ofRawInt {α : Q(Type u)} (n : ℤ) (e : Q($α)) : Result e :=
  if 0 ≤ n then
    Result.ofRawNat e
  else Id.run do
    let .app (.app _ (rα : Q(Ring $α))) (.app _ (lit : Q(ℕ))) := e | panic! "not a raw int cast"
    .isNegNat rα lit (q(IsInt.of_raw $α (.negOfNat $lit)) : Expr)

/-- Constructs a `Result` out of a raw rat cast.
Assumes `e` is a raw rat cast expression denoting `n`. -/
/-
**Mathlib.Meta.NormNum.Result.ofRawNNRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta
.NormNum.Result`。
形式化陈述：{u : Level} → {α : Q(Type u)} → ℚ → (e : Q(«$α»)) → optParam (Option Expr)
 none → Mathlib.Meta.NormNum.Result e
参数：Type u；e : Q(«$α»)；Option Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a `Result` out of a raw rat cast.
Assumes `e` is a raw rat cast expression denoting `n`.
-/
def Result.ofRawNNRat
    {α : Q(Type u)} (q : ℚ) (e : Q($α)) (hyp : Option Expr := none) : Result e :=
  if q.den = 1 then
    Result.ofRawNat e
  else Id.run do
    let .app (.app (.app _ (dα : Q(DivisionSemiring $α))) (n : Q(ℕ))) (d : Q(ℕ)) := e
      | panic! "not a raw nnrat cast"
    let hyp : Q(($d : $α) ≠ 0) := hyp.get!
    .isNNRat dα q n d (q(IsNNRat.of_raw $α $n $d $hyp) : Expr)

/-- Constructs a `Result` out of a raw rat cast.
Assumes `e` is a raw rat cast expression denoting `n`. -/
/-
**Mathlib.Meta.NormNum.Result.ofRawRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum.Result`。
形式化陈述：{u : Level} → {α : Q(Type u)} → ℚ → (e : Q(«$α»)) → optParam (Option Expr)
 none → Mathlib.Meta.NormNum.Result e
参数：Type u；e : Q(«$α»)；Option Expr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a `Result` out of a raw rat cast.
Assumes `e` is a raw rat cast expression denoting `n`.
-/
def Result.ofRawRat {α : Q(Type u)} (q : ℚ) (e : Q($α)) (hyp : Option Expr := none) : Result e :=
  if q.den = 1 then
    Result.ofRawInt q.num e
  else if 0 ≤ q then
    Result.ofRawNNRat q e hyp
  else Id.run do
    let .app (.app (.app _ (dα : Q(DivisionRing $α))) (.app _ (n : Q(ℕ)))) (d : Q(ℕ)) := e
      | panic! "not a raw rat cast"
    let hyp : Q(($d : $α) ≠ 0) := hyp.get!
    .isNegNNRat dα q n d (q(IsRat.of_raw $α (.negOfNat $n) $d $hyp) : Expr)

/-- Convert a `Result` to a `Simp.Result`. -/
/-
**Mathlib.Meta.NormNum.Result.toSimpResult** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Me
ta.NormNum.Result`。
形式化陈述：{u : Level} → {α : Q(Type u)} → {e : Q(«$α»)} → Mathlib.Meta.NormNum.Resul
t e → MetaM Meta.Simp.Result
参数：Type u；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a `Result` to a `Simp.Result`.
-/
def Result.toSimpResult {α : Q(Type u)} {e : Q($α)} : Result e → MetaM Simp.Result
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

/-- Given `Mathlib.Meta.NormNum.Result.isBool p b`, this is the type of `p`.
  Note that `BoolResult p b` is definitionally equal to `Expr`, and if you write `match b with ...`,
  then in the `true` branch `BoolResult p true` is reducibly equal to `Q($p)` and
  in the `false` branch it is reducibly equal to `Q(¬ $p)`. -/
/-
**Mathlib.Meta.NormNum.BoolResult** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：BoolResult (p : Q(Prop)) (b : Bool) : Type
参数：p : Q(Prop)；b : Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Mathlib.Meta.NormNum.Result.isBool p b`, this is the type of `p`.
  Note that `BoolResult p b` is definitionally equal to `Expr`, and if you write
 `match b with ...`,
  then in the `true` branch `BoolResult p true` is reducibly equal to `Q($p)` an
d
  in the `false` branch it is reducibly equal to `Q(¬ $p)`.
-/
abbrev BoolResult (p : Q(Prop)) (b : Bool) : Type :=
  Q(Bool.rec (¬ $p) ($p) $b)

/-- Obtain a `Result` from a `BoolResult`. -/
/-
**Mathlib.Meta.NormNum.Result.ofBoolResult** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Me
ta.NormNum.Result`。
形式化陈述：{p : Q(Prop)} → {b : Bool} → Mathlib.Meta.NormNum.BoolResult p b → Mathlib
.Meta.NormNum.Result q(Prop)
参数：Prop；Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Obtain a `Result` from a `BoolResult`.
-/
def Result.ofBoolResult {p : Q(Prop)} {b : Bool} (prf : BoolResult p b) : Result q(Prop) :=
  Result'.isBool b prf

/-- If `a = b` and we can evaluate `b`, then we can evaluate `a`. -/
/-
**Mathlib.Meta.NormNum.Result.eqTrans** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} → {a b : Q(«$α»)} → Q(«$a» = «$b») → Mathl
ib.Meta.NormNum.Result b → Mathlib.Meta.NormNum.Result a
参数：Type u；«$α»；«$a» = «$b»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a = b` and we can evaluate `b`, then we can evaluate `a`.
-/
def Result.eqTrans {α : Q(Type u)} {a b : Q($α)} (eq : Q($a = $b)) : Result b → Result a
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

