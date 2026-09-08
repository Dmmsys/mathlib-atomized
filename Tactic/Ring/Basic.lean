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
/-
**Mathlib.Tactic.Ring.ExBase** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：ExBase
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ExBase := Common.ExBase RatCoeff sα
@[expose, reducible, inherit_doc Common.ExProd]
/-
**Mathlib.Tactic.Ring.ExProd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：ExProd
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ExProd := Common.ExProd RatCoeff sα
@[expose, reducible, inherit_doc Common.ExSum]
/-
**Mathlib.Tactic.Ring.ExSum** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：ExSum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ExSum := Common.ExSum RatCoeff sα

section
variable {R : Type*} [CommSemiring R] {a : R}

/-
**Mathlib.Tactic.Ring.cast_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a : R} {n : ℕ}, Mathlib.Meta.Nor
mNum.IsNat a n → a = n.rawCast + 0
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
theorem cast_pos {n : ℕ} : IsNat (a : R) n → a = n.rawCast + 0
  | ⟨e⟩ => by simp [e]
/-
**Mathlib.Tactic.Ring.cast_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {a : R}, Mathlib.Meta.NormNum.IsN
at a 0 → a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_zero : IsNat (a : R) (nat_lit 0) → a = 0
  | ⟨e⟩ => by simp [e]
/-
**Mathlib.Tactic.Ring.cast_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：∀ {n : ℕ} {R : Type u_2} [inst : Ring R] {a : R},   Mathlib.Meta.NormNum.I
sInt a (Int.negOfNat n) → a = (Int.negOfNat n).rawCast + 0
参数：Int.negOfNat n；Int.negOfNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_neg {n : ℕ} {R} [Ring R] {a : R} :
    IsInt a (.negOfNat n) → a = (Int.negOfNat n).rawCast + 0
  | ⟨e⟩ => by simp [e]
/-
**Mathlib.Tactic.Ring.cast_nnrat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring`
。
形式化陈述：∀ {n d : ℕ} {R : Type u_2} [inst : DivisionSemiring R] {a : R},   Mathlib.
Meta.NormNum.IsNNRat a n d → a = NNRat.rawCast n d + 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_nnrat {n : ℕ} {d : ℕ} {R} [DivisionSemiring R] {a : R} :
    IsNNRat a n d → a = NNRat.rawCast n d + 0
  | ⟨_, e⟩ => by simp [e, div_eq_mul_inv]
/-
**Mathlib.Tactic.Ring.cast_rat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：∀ {n : ℤ} {d : ℕ} {R : Type u_2} [inst : DivisionRing R] {a : R},   Mathli
b.Meta.NormNum.IsRat a n d → a = Rat.rawCast n d + 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_rat {n : ℤ} {d : ℕ} {R} [DivisionRing R] {a : R} :
    IsRat a n d → a = Rat.rawCast n d + 0
  | ⟨_, e⟩ => by simp [e, div_eq_mul_inv]

end

section
/--
Constructs the expression corresponding to `.const n`.
(The `.const` constructor does not check that the expression is correct.)
-/
/-
**Mathlib.Tactic.Ring.ExProd.mkNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Rin
g.ExProd`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (sα : Q(CommSemiring «$α»)) → ℕ → (e : Q(«
$α»)) × Mathlib.Tactic.Ring.ExProd sα e
参数：Type u；sα : Q(CommSemiring «$α»)；e : Q(«$α»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs the expression corresponding to `.const n`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNat (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := .lit (.natVal n)
  ⟨q(($lit).rawCast : $α), .const ⟨n, none⟩⟩

/--
Constructs the expression corresponding to `.const (-n)`.
(The `.const` constructor does not check that the expression is correct.)
-/
/-
**Mathlib.Tactic.Ring.ExProd.mkNegNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
Ring.ExProd`。
形式化陈述：{u : Level} →   {α : Q(Type u)} → (sα : Q(CommSemiring «$α»)) → Q(Ring «$α
») → ℕ → (e : Q(«$α»)) × Mathlib.Tactic.Ring.ExProd sα e
参数：Type u；sα : Q(CommSemiring «$α»)；Ring «$α»；e : Q(«$α»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs the expression corresponding to `.const (-n)`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNegNat (_ : Q(Ring $α)) (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := mkRawNatLit n
  ⟨q((Int.negOfNat $lit).rawCast : $α), .const ⟨(-n), none⟩⟩

/--
Constructs the expression corresponding to `.const q h` for `q = n / d`
and `h` a proof that `(d : α) ≠ 0`.
(The `.const` constructor does not check that the expression is correct.)
-/
/-
**Mathlib.Tactic.Ring.ExProd.mkNNRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.R
ing.ExProd`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
Q(DivisionSemiring «$α») → ℚ → Q(ℕ) → Q(ℕ) → Expr → (e : Q(«$α»)) × Mathlib.Tact
ic.Ring.ExProd sα e
参数：Type u；sα : Q(CommSemiring «$α»)；DivisionSemiring «$α»；ℕ；ℕ；e : Q(«$α»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs the expression corresponding to `.const q h` for `q = n / d`
and `h` a proof that `(d : α) ≠ 0`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNNRat (_ : Q(DivisionSemiring $α)) (q : ℚ) (n : Q(ℕ)) (d : Q(ℕ)) (h : Expr) :
    (e : Q($α)) × ExProd sα e :=
  ⟨q(NNRat.rawCast $n $d : $α), .const ⟨q, h⟩⟩

/--
Constructs the expression corresponding to `.const q h` for `q = -(n / d)`
and `h` a proof that `(d : α) ≠ 0`.
(The `.const` constructor does not check that the expression is correct.)
-/
/-
**Mathlib.Tactic.Ring.ExProd.mkNegNNRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.Ring.ExProd`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
Q(DivisionRing «$α») → ℚ → Q(ℕ) → Q(ℕ) → Expr → (e : Q(«$α»)) × Mathlib.Tactic.R
ing.ExProd sα e
参数：Type u；sα : Q(CommSemiring «$α»)；DivisionRing «$α»；ℕ；ℕ；e : Q(«$α»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs the expression corresponding to `.const q h` for `q = -(n / d)`
and `h` a proof that `(d : α) ≠ 0`.
(The `.const` constructor does not check that the expression is correct.)
-/
def ExProd.mkNegNNRat (_ : Q(DivisionRing $α)) (q : ℚ) (n : Q(ℕ)) (d : Q(ℕ)) (h : Expr) :
    (e : Q($α)) × ExProd sα e :=
  ⟨q(Rat.rawCast (.negOfNat $n) $d : $α), .const ⟨q, h⟩⟩
end

/-- Converts a proof by `norm_num` that `e` is a numeral, into a normalization as a monomial:

* `e = 0` if `norm_num` returns `IsNat e 0`
* `e = Nat.rawCast n + 0` if `norm_num` returns `IsNat e n`
* `e = Int.rawCast n + 0` if `norm_num` returns `IsInt e n`
* `e = NNRat.rawCast n d + 0` if `norm_num` returns `IsNNRat e n d`
* `e = Rat.rawCast n d + 0` if `norm_num` returns `IsRat e n d`
-/
/-
**Mathlib.Tactic.Ring.evalCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：evalCast {α : Q(Type u)} (sα : Q(CommSemiring $α)) {e : Q($α)} : NormNum.R
esult e -> Option (Result (ExSum sα) e) | .isNat _ (.lit (.natVal 0)) p => do as
sumeInstancesCommute pure ⟨_, .zero, q(cast_zero $p)⟩ | .isNat _ lit p => do ass
umeInstancesCommute have ⟨e', s⟩
参数：Type u；sα : Q(CommSemiring $α)；$α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a proof by `norm_num` that `e` is a numeral, into a normalization as a 
monomial:

* `e = 0` if `norm_num` returns `IsNat e 0`
* `e = Nat.rawCast n + 0` if `norm_num` returns `IsNat e n`
* `e = Int.rawCast n + 0` if `norm_num` returns `IsInt e n`
* `e = NNRat.rawCast n d + 0` if `norm_num` returns `IsNNRat e n d`
* `e = Rat.rawCast n d + 0` if `norm_num` returns `IsRat e n d`
-/
def evalCast {α : Q(Type u)} (sα : Q(CommSemiring $α)) {e : Q($α)} :
    NormNum.Result e → Option (Result (ExSum sα) e)
  | .isNat _ (.lit (.natVal 0)) p => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(cast_zero $p)⟩
  | .isNat _ lit p => do
    assumeInstancesCommute
    have ⟨e', s⟩ := ExProd.mkNat sα lit.natLit!
    have : $e' =Q ($lit).rawCast := ⟨⟩
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

variable {R : Type*} [CommSemiring R] {n : ℕ} {a₁ a₂ a₃ : ℕ} {b₁ b₂ b₃ : R}

/-! ### Scalar multiplication by `ℕ` -/

/-
**Mathlib.Tactic.Ring.natCast_nat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring
`。
形式化陈述：natCast_nat (n) : ((Nat.rawCast n : Nat) : R) = Nat.rawCast n
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Scalar multiplication by `ℕ`
-/
theorem natCast_nat (n) : ((Nat.rawCast n : ℕ) : R) = Nat.rawCast n := by simp
/-
**Mathlib.Tactic.Ring.natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring
`。
形式化陈述：natCast_mul {a₁ a₃ : Nat} (a₂) (_ : ((a₁ : Nat) : R) = b₁) (_ : ((a₃ : Nat
) : R) = b₃) : ((a₁ ^ a₂ * a₃ : Nat) : R) = b₁ ^ a₂ * b₃
参数：a₂；_ : ((a₁ : Nat) : R) = b₁；_ : ((a₃ : Nat) : R) = b₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natCast_mul {a₁ a₃ : ℕ} (a₂) (_ : ((a₁ : ℕ) : R) = b₁)
    (_ : ((a₃ : ℕ) : R) = b₃) : ((a₁ ^ a₂ * a₃ : ℕ) : R) = b₁ ^ a₂ * b₃ := by
  subst_vars; simp
/-
**Mathlib.Tactic.Ring.natCast_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Rin
g`。
形式化陈述：natCast_zero : ((0 : Nat) : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem natCast_zero : ((0 : ℕ) : R) = 0 := Nat.cast_zero
/-
**Mathlib.Tactic.Ring.natCast_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring
`。
形式化陈述：natCast_add {a₁ a₂ : Nat} (_ : ((a₁ : Nat) : R) = b₁) (_ : ((a₂ : Nat) : R
) = b₂) : ((a₁ + a₂ : Nat) : R) = b₁ + b₂
参数：_ : ((a₁ : Nat) : R) = b₁；_ : ((a₂ : Nat) : R) = b₂。
该定理/引理给出了一组等式。
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
theorem natCast_add {a₁ a₂ : ℕ}
    (_ : ((a₁ : ℕ) : R) = b₁) (_ : ((a₂ : ℕ) : R) = b₂) : ((a₁ + a₂ : ℕ) : R) = b₁ + b₂ := by
  subst_vars; simp

mutual -- partial only to speed up compilation

variable {v : Lean.Level} {β : Q(Type v)} (sβ : Q(CommSemiring $β))
  (_ : v =QL 0) (_ : $β =Q ℕ) (_ : $sβ =Q inferInstance)

/-- Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

* An atom `e` causes `↑e` to be allocated as a new atom.
* A sum delegates to `ExSum.evalNatCast`.
-/
/-
**Mathlib.Tactic.Ring.ExBase.evalNatCast** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.T
actic.Ring.ExBase`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{v : Level} →         {β : Q(Type v)} →           (sβ : Q(CommSemiring «$β»)) → 
            {a : Q(ℕ)} →               Mathlib.Tactic.Ring.ExBase sβ a →        
         Mathlib.Tactic.AtomM (Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic
.Ring.ExBase sα) q(↑«$a»))
参数：Type u；sα : Q(CommSemiring «$α»)；Type v；sβ : Q(CommSemiring «$β»)；ℕ；Mathlib.T
actic.Ring.Common.Result (Mathlib.Tactic.Ring.ExBase sα) q(↑«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

* An atom `e` causes `↑e` to be allocated as a new atom.
* A sum delegates to `ExSum.evalNatCast`.
-/
partial def ExBase.evalNatCast {a : Q(ℕ)} (va : ExBase sβ a) : AtomM (Result (ExBase sα) q($a)) :=
  match va with
  | .atom _ => do
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalNatCast va
    pure ⟨_, .sum vc, p⟩

/-- Applies `Nat.cast` to a nat monomial to produce a monomial in `α`.

* `↑c = c` if `c` is a numeric literal
* `↑(a ^ n * b) = ↑a ^ n * ↑b`
-/
/-
**Mathlib.Tactic.Ring.ExProd.evalNatCast** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.T
actic.Ring.ExProd`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{v : Level} →         {β : Q(Type v)} →           (sβ : Q(CommSemiring «$β»)) → 
            {a : Q(ℕ)} →               Mathlib.Tactic.Ring.ExProd sβ a →        
         Mathlib.Tactic.AtomM (Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic
.Ring.ExProd sα) q(↑«$a»))
参数：Type u；sα : Q(CommSemiring «$α»)；Type v；sβ : Q(CommSemiring «$β»)；ℕ；Mathlib.T
actic.Ring.Common.Result (Mathlib.Tactic.Ring.ExProd sα) q(↑«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `Nat.cast` to a nat monomial to produce a monomial in `α`.

* `↑c = c` if `c` is a numeric literal
* `↑(a ^ n * b) = ↑a ^ n * ↑b`
-/
partial def ExProd.evalNatCast {a : Q(ℕ)} (va : ExProd sβ a) : AtomM (Result (ExProd sα) q($a)) :=
  match va with
  | .const ⟨c, hc⟩ =>
    have n : Q(ℕ) := a.appArg!
    have : $a =Q Nat.rawCast $n := ⟨⟩
    pure ⟨q(Nat.rawCast $n), .const ⟨c, hc⟩, q(natCast_nat (R := $α) $n)⟩
  | .mul (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalNatCast va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalNatCast va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, q(natCast_mul $a₂ $pb₁ $pb₃)⟩

/-- Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

* `↑0 = 0`
* `↑(a + b) = ↑a + ↑b`
-/
/-
**Mathlib.Tactic.Ring.ExSum.evalNatCast** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Ta
ctic.Ring.ExSum`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{v : Level} →         {β : Q(Type v)} →           (sβ : Q(CommSemiring «$β»)) → 
            {a : Q(ℕ)} →               Mathlib.Tactic.Ring.ExSum sβ a →         
        Mathlib.Tactic.AtomM (Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.
Ring.ExSum sα) q(↑«$a»))
参数：Type u；sα : Q(CommSemiring «$α»)；Type v；sβ : Q(CommSemiring «$β»)；ℕ；Mathlib.T
actic.Ring.Common.Result (Mathlib.Tactic.Ring.ExSum sα) q(↑«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `Nat.cast` to a nat polynomial to produce a polynomial in `α`.

* `↑0 = 0`
* `↑(a + b) = ↑a + ↑b`
-/
partial def ExSum.evalNatCast {a : Q(ℕ)} (va : ExSum sβ a) : AtomM (Result (ExSum sα) q($a)) := do
  assumeInstancesCommute
  match (dependent := true) va with
  | .zero => pure ⟨_, .zero, q(natCast_zero (R := $α))⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← ExProd.evalNatCast va₁
    let ⟨_, vb₂, pb₂⟩ ← ExSum.evalNatCast va₂
    pure ⟨_, .add vb₁ vb₂, q(natCast_add $pb₁ $pb₂)⟩

end

/-! ### Scalar multiplication by `ℤ` -/

/-
**Mathlib.Tactic.Ring.natCast_int** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring
`。
形式化陈述：natCast_int {R} [CommRing R] (n) : ((Nat.rawCast n : Int) : R) = Nat.rawCa
st n
参数：n。
该定理/引理给出了一组等式。
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
### Scalar multiplication by `ℤ`
-/
theorem natCast_int {R} [CommRing R] (n) : ((Nat.rawCast n : ℤ) : R) = Nat.rawCast n := by simp
/-
**Mathlib.Tactic.Ring.intCast_negOfNat_Int** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.Ring`。
形式化陈述：intCast_negOfNat_Int {R} [CommRing R] (n) : ((Int.rawCast (Int.negOfNat n)
 : Int) : R) = Int.rawCast (Int.negOfNat n)
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intCast_negOfNat_Int {R} [CommRing R] (n) :
    ((Int.rawCast (Int.negOfNat n) : ℤ) : R) = Int.rawCast (Int.negOfNat n) := by simp
/-
**Mathlib.Tactic.Ring.intCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring
`。
形式化陈述：intCast_mul {R} [CommRing R] {b₁ b₃ : R} {a₁ a₃ : Int} (a₂) (_ : ((a₁ : In
t) : R) = b₁) (_ : ((a₃ : Int) : R) = b₃) : ((a₁ ^ a₂ * a₃ : Int) : R) = b₁ ^ a₂
 * b₃
参数：a₂；_ : ((a₁ : Int) : R) = b₁；_ : ((a₃ : Int) : R) = b₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intCast_mul {R} [CommRing R] {b₁ b₃ : R} {a₁ a₃ : ℤ} (a₂) (_ : ((a₁ : ℤ) : R) = b₁)
    (_ : ((a₃ : ℤ) : R) = b₃) : ((a₁ ^ a₂ * a₃ : ℤ) : R) = b₁ ^ a₂ * b₃ := by
  subst_vars; simp
/-
**Mathlib.Tactic.Ring.intCast_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Rin
g`。
形式化陈述：intCast_zero {R} [CommRing R] : ((0 : Int) : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
-/
theorem intCast_zero {R} [CommRing R] : ((0 : ℤ) : R) = 0 := Int.cast_zero
/-
**Mathlib.Tactic.Ring.intCast_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring
`。
形式化陈述：intCast_add {R} [CommRing R] {b₁ b₂ : R} {a₁ a₂ : Int} (_ : ((a₁ : Int) : 
R) = b₁) (_ : ((a₂ : Int) : R) = b₂) : ((a₁ + a₂ : Int) : R) = b₁ + b₂
参数：_ : ((a₁ : Int) : R) = b₁；_ : ((a₂ : Int) : R) = b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intCast_add {R} [CommRing R] {b₁ b₂ : R} {a₁ a₂ : ℤ}
    (_ : ((a₁ : ℤ) : R) = b₁) (_ : ((a₂ : ℤ) : R) = b₂) : ((a₁ + a₂ : ℤ) : R) = b₁ + b₂ := by
  subst_vars; simp


mutual

variable {v : Lean.Level} {β : Q(Type v)} (sβ : Q(CommSemiring $β))
  (_ : v =QL 0) (_ : $β =Q ℤ) (_ : $sβ =Q inferInstance)

/-- Applies `Int.cast` to an int polynomial to produce a polynomial in `α`.

* An atom `e` causes `↑e` to be allocated as a new atom.
* A sum delegates to `ExSum.evalIntCast`.
-/
/-
**Mathlib.Tactic.Ring.ExBase.evalIntCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Ring.ExBase`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{v : Level} →         {β : Q(Type v)} →           (sβ : Q(CommSemiring «$β»)) → 
            {a : Q(ℤ)} →               (rα : Q(CommRing «$α»)) →                
 Mathlib.Tactic.Ring.ExBase sβ a →                   Mathlib.Tactic.AtomM (Mathl
ib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.ExBase sα) q(↑«$a»))
参数：Type u；sα : Q(CommSemiring «$α»)；Type v；sβ : Q(CommSemiring «$β»)；ℤ；rα : Q(Co
mmRing «$α»)；Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.ExBase sα) q
(↑«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `Int.cast` to an int polynomial to produce a polynomial in `α`.

* An atom `e` causes `↑e` to be allocated as a new atom.
* A sum delegates to `ExSum.evalIntCast`.
-/
def ExBase.evalIntCast {a : Q(ℤ)} (rα : Q(CommRing $α)) (va : ExBase sβ a) :
    AtomM (Result (ExBase sα) q($a)) :=
  match va with
  | .atom _ => do
    assumeInstancesCommute
    let (i, ⟨b', _⟩) ← addAtomQ q($a)
    pure ⟨b', .atom i, q(Eq.refl $b')⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← ExSum.evalIntCast rα va
    pure ⟨_, .sum vc, p⟩


/-- Applies `Int.cast` to an int monomial to produce a monomial in `α`.

* `↑c = c` if `c` is a numeric literal
* `↑(a ^ n * b) = ↑a ^ n * ↑b`
-/
/-
**Mathlib.Tactic.Ring.ExProd.evalIntCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Ring.ExProd`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{v : Level} →         {β : Q(Type v)} →           (sβ : Q(CommSemiring «$β»)) → 
            {a : Q(ℤ)} →               (rα : Q(CommRing «$α»)) →                
 Mathlib.Tactic.Ring.ExProd sβ a →                   Mathlib.Tactic.AtomM (Mathl
ib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.ExProd sα) q(↑«$a»))
参数：Type u；sα : Q(CommSemiring «$α»)；Type v；sβ : Q(CommSemiring «$β»)；ℤ；rα : Q(Co
mmRing «$α»)；Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.ExProd sα) q
(↑«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `Int.cast` to an int monomial to produce a monomial in `α`.

* `↑c = c` if `c` is a numeric literal
* `↑(a ^ n * b) = ↑a ^ n * ↑b`
-/
def ExProd.evalIntCast {a : Q(ℤ)} (rα : Q(CommRing $α)) (va : ExProd sβ a) :
    AtomM (Result (ExProd sα) q($a)) :=
  match va with
  | .const ⟨c, hc⟩ => do
    match a with
    | ~q(Nat.rawCast $m) =>
      pure ⟨q(Nat.rawCast $m), .const ⟨c, hc⟩, q(natCast_int (R := $α) $m)⟩
    | ~q(Int.rawCast (Int.negOfNat $m)) =>
      pure ⟨q(Int.rawCast (Int.negOfNat $m)), .const ⟨c, hc⟩, q(intCast_negOfNat_Int (R := $α) $m)⟩
  | .mul (e := a₂) (x := x) (b := b) va₁ va₂ va₃ => do
    have : $a =Q $x ^ $a₂ * $b := ⟨⟩
    let ⟨_, vb₁, pb₁⟩ ← ExBase.evalIntCast rα va₁
    let ⟨_, vb₃, pb₃⟩ ← ExProd.evalIntCast rα va₃
    assumeInstancesCommute
    pure ⟨_, .mul vb₁ va₂ vb₃, (q(intCast_mul $a₂ $pb₁ $pb₃))⟩

/-- Applies `Int.cast` to an int polynomial to produce a polynomial in `α`.

* `↑0 = 0`
* `↑(a + b) = ↑a + ↑b`
-/
/-
**Mathlib.Tactic.Ring.ExSum.evalIntCast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.Ring.ExSum`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{v : Level} →         {β : Q(Type v)} →           (sβ : Q(CommSemiring «$β»)) → 
            {a : Q(ℤ)} →               (rα : Q(CommRing «$α»)) →                
 Mathlib.Tactic.Ring.ExSum sβ a →                   Mathlib.Tactic.AtomM (Mathli
b.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.ExSum sα) q(↑«$a»))
参数：Type u；sα : Q(CommSemiring «$α»)；Type v；sβ : Q(CommSemiring «$β»)；ℤ；rα : Q(Co
mmRing «$α»)；Mathlib.Tactic.Ring.Common.Result (Mathlib.Tactic.Ring.ExSum sα) q(
↑«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `Int.cast` to an int polynomial to produce a polynomial in `α`.

* `↑0 = 0`
* `↑(a + b) = ↑a + ↑b`
-/
def ExSum.evalIntCast {a : Q(ℤ)} (rα : Q(CommRing $α))
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

/-- Converts `ExBase sα` to `ExBase sβ`, assuming `sα` and `sβ` are defeq. -/
/-
**Mathlib.Tactic.Ring.ExBase.cast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring
.ExBase`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{v : Level} →         {β : Q(Type v)} →           {sβ : Q(CommSemiring «$β»)} → 
            {a : Q(«$α»)} → Mathlib.Tactic.Ring.ExBase sα a → (a : Q(«$β»)) × Ma
thlib.Tactic.Ring.ExBase sβ a
参数：Type u；sα : Q(CommSemiring «$α»)；Type v；CommSemiring «$β»；«$α»；a : Q(«$β»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts `ExBase sα` to `ExBase sβ`, assuming `sα` and `sβ` are defeq.
-/
def ExBase.cast
    {v : Lean.Level} {β : Q(Type v)} {sβ : Q(CommSemiring $β)} {a : Q($α)} :
    ExBase sα a → Σ a, ExBase sβ a
  | .atom i => ⟨a, .atom i⟩
  | .sum a => let ⟨_, vb⟩ := ExSum.cast a; ⟨_, .sum vb⟩

/-- Converts `ExProd sα` to `ExProd sβ`, assuming `sα` and `sβ` are defeq. -/
/-
**Mathlib.Tactic.Ring.ExProd.cast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring
.ExProd`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{v : Level} →         {β : Q(Type v)} →           {sβ : Q(CommSemiring «$β»)} → 
            {a : Q(«$α»)} → Mathlib.Tactic.Ring.ExProd sα a → (a : Q(«$β»)) × Ma
thlib.Tactic.Ring.ExProd sβ a
参数：Type u；sα : Q(CommSemiring «$α»)；Type v；CommSemiring «$β»；«$α»；a : Q(«$β»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts `ExProd sα` to `ExProd sβ`, assuming `sα` and `sβ` are defeq.
-/
def ExProd.cast
    {v : Lean.Level} {β : Q(Type v)} {sβ : Q(CommSemiring $β)} {a : Q($α)} :
    ExProd sα a → Σ a, ExProd sβ a
  | .const ⟨i, h⟩ => ⟨a, .const ⟨i, h⟩⟩
  | .mul a₁ a₂ a₃ => ⟨_, .mul (ExBase.cast a₁).2 a₂ (ExProd.cast a₃).2⟩

/-- Converts `ExSum sα` to `ExSum sβ`, assuming `sα` and `sβ` are defeq. -/
/-
**Mathlib.Tactic.Ring.ExSum.cast** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring.
ExSum`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{v : Level} →         {β : Q(Type v)} →           {sβ : Q(CommSemiring «$β»)} → 
            {a : Q(«$α»)} → Mathlib.Tactic.Ring.ExSum sα a → (a : Q(«$β»)) × Mat
hlib.Tactic.Ring.ExSum sβ a
参数：Type u；sα : Q(CommSemiring «$α»)；Type v；CommSemiring «$β»；«$α»；a : Q(«$β»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts `ExSum sα` to `ExSum sβ`, assuming `sα` and `sβ` are defeq.
-/
def ExSum.cast
    {v : Lean.Level} {β : Q(Type v)} {sβ : Q(CommSemiring $β)} {a : Q($α)} :
    ExSum sα a → Σ a, ExSum sβ a
  | .zero => ⟨_, .zero⟩
  | .add a₁ a₂ => ⟨_, .add (ExProd.cast a₁).2 (ExSum.cast a₂).2⟩

end

/-
**Mathlib.Tactic.Ring.smul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring
`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] {a a' : α}, a = a' → ∀ (b : α), a • b = a'
 * b
参数：b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_eq_mul {α : Type*} [Mul α] {a a' : α} (h : a = a') (b : α) : a • b = a' * b := by
  subst h
  rfl
/-
**Mathlib.Tactic.Ring.Nat.smul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Nat`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n n' : ℕ} {r : R}, ↑n = r → n' =
 n → ∀ (a : R), n' • a = r * a
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Nat.smul_eq_mul {n n' : ℕ} {r : R} (hr : n = r) (hn : n' = n) (a : R) : n' • a = r * a := by
  subst_vars
  simp only [nsmul_eq_mul]
/-
**Mathlib.Tactic.Ring.Int.smul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Ring.Int`。
形式化陈述：∀ {R : Type u_2} {n n' : ℤ} {r : R} [inst : CommRing R], ↑n = r → n' = n →
 ∀ (a : R), n' • a = r * a
参数：a : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Int.smul_eq_mul {R} {n n' : ℤ} {r : R} [CommRing R] (hr : n = r) (hn : n' = n) (a : R) :
    n' • a = r * a := by
  subst_vars
  simp only [zsmul_eq_mul]

/-- Turn coefficient data into a NormNum.Result. -/
/-
**Mathlib.Tactic.Ring.RatCoeff.toResult** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.Ring.RatCoeff`。
形式化陈述：{u : Level} → {α : Q(Type u)} → {a : Q(«$α»)} → Mathlib.Tactic.Ring.RatCoe
ff a → Mathlib.Meta.NormNum.Result a
参数：Type u；«$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn coefficient data into a NormNum.Result.
-/
def RatCoeff.toResult {a : Q($α)} : RatCoeff a → NormNum.Result a
| ⟨q, h⟩ => Result.ofRawRat q a h

/-- Turn a NormNum.Result into coefficient data. -/
/-
**Mathlib.Tactic.Ring.RatCoeff.ofResult** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.Ring.RatCoeff`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {a : Q(«$α»)} →       Mathlib.Meta.N
ormNum.Result a → Option (Mathlib.Tactic.Ring.Common.Result Mathlib.Tactic.Ring.
RatCoeff a)
参数：Type u；«$α»；Mathlib.Tactic.Ring.Common.Result Mathlib.Tactic.Ring.RatCoeff a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a NormNum.Result into coefficient data.
-/
def RatCoeff.ofResult {a : Q($α)} (res : NormNum.Result a) : Option <| Result RatCoeff a := do
  let ⟨qc, hc⟩ ← res.toRatNZ
  let ⟨c, pc⟩ := res.toRawEq
  return ⟨q($c), ⟨qc, hc⟩, q($pc)⟩

namespace RingCompute
mutual

/-- Add two rational number expressions. If the result is zero, returns a proof of this fact. -/
/-
**Mathlib.Tactic.Ring.RingCompute.add** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
Ring.RingCompute`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{a b : Q(«$α»)} →         Mathlib.Tactic.Ring.RatCoeff a →           Mathlib.Tac
tic.Ring.RatCoeff b →             MetaM               (Mathlib.Tactic.Ring.Commo
n.Result Mathlib.Tactic.Ring.RatCoeff q(«$a» + «$b») ×                 Option Q(
Mathlib.Meta.NormNum.IsNat («$a» + «$b») 0))
参数：Type u；sα : Q(CommSemiring «$α»)；«$α»；Mathlib.Tactic.Ring.Common.Result Mathl
ib.Tactic.Ring.RatCoeff q(«$a» + «$b») ×                 Option Q(Mathlib.Meta.N
ormNum.IsNat («$a» + «$b») 0)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add two rational number expressions. If the result is zero, returns a proof of t
his fact.
-/
partial def add {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    {a b : Q($α)} (za : RatCoeff a) (zb : RatCoeff b) :
    MetaM (Result RatCoeff q($a + $b) × Option Q(IsNat ($a + $b) 0)) := do
  let res ← za.toResult.add zb.toResult
  let isZero ← match res with
    | Result.isNat _inst lit pf =>
      if lit.natLit! == 0 then
        pure <| some (pf : Q(IsNat ($a + $b) 0))
      else
        pure none
    | _ => pure none
  let r ← RatCoeff.ofResult res
  return ⟨r, isZero⟩

/-- Evaluate the product of two rational number expressions. -/
/-
**Mathlib.Tactic.Ring.RingCompute.mul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
Ring.RingCompute`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{a b : Q(«$α»)} →         Mathlib.Tactic.Ring.RatCoeff a →           Mathlib.Tac
tic.Ring.RatCoeff b →             MetaM (Mathlib.Tactic.Ring.Common.Result Mathl
ib.Tactic.Ring.RatCoeff q(«$a» * «$b»))
参数：Type u；sα : Q(CommSemiring «$α»)；«$α»；Mathlib.Tactic.Ring.Common.Result Mathl
ib.Tactic.Ring.RatCoeff q(«$a» * «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate the product of two rational number expressions.
-/
partial def mul {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    {a b : Q($α)} (za : RatCoeff a) (zb : RatCoeff b) :
    MetaM (Result RatCoeff q($a * $b)) := do
  let res ← za.toResult.mul zb.toResult
  return ← RatCoeff.ofResult res

/-- Cast ℕ and ℤ normalized expressions ExSums into `α`, used to evaluate scalar multiplications. -/
/-
**Mathlib.Tactic.Ring.RingCompute.cast** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tac
tic.Ring.RingCompute`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
Mathlib.Tactic.Ring.Common.Cache sα →         (v : Level) →           (β : Q(Typ
e v)) →             Q(CommSemiring «$β») →               (_smul : Q(SMul «$β» «$
α»)) →                 (x : Q(«$β»)) →                   Mathlib.Tactic.AtomM   
                  ((y : Q(«$α»)) ×                       Mathlib.Tactic.Ring.Com
mon.ExSum Mathlib.Tactic.Ring.RatCoeff sα q(«$y») ×                         Q(∀ 
(a : «$α»), «$x» • a = «$y» * a))
参数：Type u；sα : Q(CommSemiring «$α»)；v : Level；β : Q(Type v)；CommSemiring «$β»；_s
mul : Q(SMul «$β» «$α»)；x : Q(«$β»)；(y : Q(«$α»)) ×                       Mathli
b.Tactic.Ring.Common.ExSum Mathlib.Tactic.Ring.RatCoeff sα q(«$y») ×            
             Q(∀ (a : «$α»), «$x» • a = «$y» * a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast ℕ and ℤ normalized expressions ExSums into `α`, used to evaluate scalar mul
tiplications.
-/
partial def cast {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) (cα : Common.Cache sα)
    (v : Lean.Level) (β : Q(Type v)) (sβ : Q(CommSemiring $β)) (_smul : Q(SMul $β $α))
    (x : Q($β)) :
    AtomM ((y : Q($α)) × Common.ExSum RatCoeff sα q($y) ×
      Q(∀ (a : $α), $x • a = $y * a)) := do
  let cβ ← Common.mkCache sβ
  let ⟨x', vx, px⟩ ← Common.eval (ringCompute .nat) (ringCompute cβ) cβ x
  if (← isDefEq sα sβ) then
    have : u =QL v := ⟨⟩
    have : $α =Q $β := ⟨⟩
    have : $sα =Q $sβ := ⟨⟩
    let ⟨b, vb⟩ := (ExSum.cast (u := v) (v := u) (sα := sβ) (sβ := sα) vx)
    have : $b =Q $x' := ⟨⟩
    assumeInstancesCommute
    return ⟨_, vb, q(smul_eq_mul $px)⟩
  match v, β, sβ, cα.rα with
  | 0, ~q(ℕ), ~q(inferInstance), _ =>
    let ⟨y, vy, py⟩ ← ExSum.evalNatCast sα sβ vx
    assumeInstancesCommute
    return ⟨y, vy, q(Nat.smul_eq_mul $py $px)⟩
  | 0, ~q(ℤ), ~q(inferInstance), some rα =>
    let ⟨y, vy, py⟩ ← ExSum.evalIntCast sα sβ rα vx
    assumeInstancesCommute
    return ⟨y, vy, q(Int.smul_eq_mul $py $px)⟩
  | _ => failure

/-- Negate rational number expressions. -/
/-
**Mathlib.Tactic.Ring.RingCompute.neg** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
Ring.RingCompute`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {a : Q(«$α»)} →       (_crα : Q(Comm
Ring «$α»)) →         Mathlib.Tactic.Ring.RatCoeff a → MetaM (Mathlib.Tactic.Rin
g.Common.Result Mathlib.Tactic.Ring.RatCoeff q(-«$a»))
参数：Type u；«$α»；_crα : Q(CommRing «$α»)；Mathlib.Tactic.Ring.Common.Result Mathlib
.Tactic.Ring.RatCoeff q(-«$a»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negate rational number expressions.
-/
partial def neg {u : Lean.Level} {α : Q(Type u)}
    {a : Q($α)} (_crα : Q(CommRing $α)) (za : RatCoeff a) :
    MetaM (Result RatCoeff q(-$a)) := do
  let res ← za.toResult.neg q(inferInstance)
  -- We have to unpack this result due to instance issues.
  let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
  return ⟨_, vc, q($pc)⟩

/-- Raise a rational number expression to the power of a natural number.

Fails if the exponent is not a literal. -/
/-
**Mathlib.Tactic.Ring.RingCompute.pow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
Ring.RingCompute`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{a : Q(«$α»)} →         {b : Q(ℕ)} →           Mathlib.Tactic.Ring.RatCoeff a → 
            Mathlib.Tactic.Ring.Common.ExProdNat q(«$b») →               OptionT
 MetaM (Mathlib.Tactic.Ring.Common.Result Mathlib.Tactic.Ring.RatCoeff q(«$a» ^ 
«$b»))
参数：Type u；sα : Q(CommSemiring «$α»)；«$α»；ℕ；«$b»；Mathlib.Tactic.Ring.Common.Resul
t Mathlib.Tactic.Ring.RatCoeff q(«$a» ^ «$b»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Raise a rational number expression to the power of a natural number.

Fails if the exponent is not a literal.
-/
partial def pow {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    {a : Q($α)} {b : Q(ℕ)} (za : RatCoeff a)
    (vb : Common.ExProdNat q($b)) :
    OptionT MetaM (Result RatCoeff q($a ^ $b)) := do
  match vb with
  | .const _ =>
    have lit : Q(ℕ) := b.appArg!
    let res ← (NormNum.evalPow.core q($a ^ $lit) q(HPow.hPow) q($a) lit lit
      q(IsNat.raw_refl $lit) q(inferInstance) za.toResult).run
    match res with
    | none => OptionT.fail
    | some res =>
      have : $b =Q $lit := ⟨⟩
      let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
      return ⟨_, vc, q($pc)⟩
  | _ => OptionT.fail

/-- Evaluate the inverse of a natural number expression. -/
/-
**Mathlib.Tactic.Ring.RingCompute.inv** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
Ring.RingCompute`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (_sα : Q(CommSemiring «$α»)) →      
 {a : Q(«$α»)} →         Option Q(CharZero «$α») →           (_sfα : Q(Semifield
 «$α»)) →             Mathlib.Tactic.Ring.RatCoeff a →               Mathlib.Tac
tic.AtomM (Option (Mathlib.Tactic.Ring.Common.Result Mathlib.Tactic.Ring.RatCoef
f q(«$a»⁻¹)))
参数：Type u；_sα : Q(CommSemiring «$α»)；«$α»；CharZero «$α»；_sfα : Q(Semifield «$α»)
；Option (Mathlib.Tactic.Ring.Common.Result Mathlib.Tactic.Ring.RatCoeff q(«$a»⁻¹
))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate the inverse of a natural number expression.
-/
partial def inv {u : Lean.Level} {α : Q(Type u)} (_sα : Q(CommSemiring $α))
    {a : Q($α)} (czα : Option Q(CharZero $α)) (_sfα : Q(Semifield $α)) (za : RatCoeff a) :
    AtomM (Option (Result RatCoeff q($a⁻¹))) := do
  match (← (Lean.observing? <| za.toResult.inv _ czα :)) with
  | some res =>
    let ⟨_, vc, pc⟩ ← RatCoeff.ofResult res
    return some ⟨_, vc, q($pc)⟩
  | none => return none

/-- Try to evaluate an expression as a rational constant using `norm_num`. -/
/-
**Mathlib.Tactic.Ring.RingCompute.derive** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Ring.RingCompute`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
(x : Q(«$α»)) →         MetaM           (Mathlib.Tactic.Ring.Common.Result (Math
lib.Tactic.Ring.Common.ExSum Mathlib.Tactic.Ring.RatCoeff sα) q(«$x»))
参数：Type u；sα : Q(CommSemiring «$α»)；x : Q(«$α»)；Mathlib.Tactic.Ring.Common.Resul
t (Mathlib.Tactic.Ring.Common.ExSum Mathlib.Tactic.Ring.RatCoeff sα) q(«$x»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Try to evaluate an expression as a rational constant using `norm_num`.
-/
partial def derive {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α)) (x : Q($α)) :
    MetaM (Result (Common.ExSum RatCoeff sα) q($x)) := do
  let res ← NormNum.derive x
  let ⟨_, va, pa⟩ ← evalCast sα res
  return ⟨_, va, q($pa)⟩

/-- Decide if `x` is 1 and provide a proof if so. -/
/-
**Mathlib.Tactic.Ring.RingCompute.isOne** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.Ring.RingCompute`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     (sα : Q(CommSemiring «$α»)) →       
{x : Q(«$α»)} → Mathlib.Tactic.Ring.RatCoeff x → Option Q(Mathlib.Meta.NormNum.I
sNat «$x» 1)
参数：Type u；sα : Q(CommSemiring «$α»)；«$α»；Mathlib.Meta.NormNum.IsNat «$x» 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Decide if `x` is 1 and provide a proof if so.
-/
partial def isOne {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    {x : Q($α)} (zx : RatCoeff x) : Option Q(IsNat $x 1) := do
  let ⟨qx, _hx⟩ := zx
  if qx == 1 then
    have : $x =Q Nat.rawCast 1 := ⟨⟩
    assumeInstancesCommute
    return q(⟨rfl⟩)
  else
    failure

/-- The comparisons on the basetype used to compare normalized ring expressions. -/
/-
**Mathlib.Tactic.Ring.RingCompute._root_.Mathlib.Tactic.Ring.ringCompare** 是 Mat
hlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring.RingCompute`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparisons on the basetype used to compare normalized ring expressions.
-/
partial def _root_.Mathlib.Tactic.Ring.ringCompare {u : Lean.Level} {α : Q(Type u)} :
    Common.RingCompare (α := α) RatCoeff where
  eq zx zy := zx.value == zy.value
  compare zx zy := compare zx.value zy.value

/-- The data used by the `ring` tactic to normalize the constant coefficients. -/
/-
**Mathlib.Tactic.Ring.RingCompute._root_.Mathlib.Tactic.Ring.ringCompute** 是 Mat
hlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring.RingCompute`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data used by the `ring` tactic to normalize the constant coefficients.
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

/-- The data used by `ring`-like tactics to normalize constant coefficients of natural number
expressions. -/
/-
**Mathlib.Tactic.Ring.rc** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data used by `ring`-like tactics to normalize constant coefficients of natur
al number
expressions.
-/
def rcℕ : Common.RingCompute (u := 0) Common.btℕ Common.sℕ := Ring.ringCompute .nat

universe u

/-- `CSLift α β` is a typeclass used by `ring` for lifting operations from `α`
(which is not a commutative semiring) into a commutative semiring `β` by using an injective map
`lift : α → β`. -/
/-
**Mathlib.Tactic.Ring.CSLift** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：Type u → outParam (Type u) → Type u
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CSLift α β` is a typeclass used by `ring` for lifting operations from `α`
(which is not a commutative semiring) into a commutative semiring `β` by using a
n injective map
`lift : α → β`.
-/
class CSLift (α : Type u) (β : outParam (Type u)) where
  /-- `lift` is the "canonical injection" from `α` to `β` -/
  lift : α → β
  /-- `lift` is an injective function -/
  inj : Function.Injective lift

/-- `CSLiftVal a b` means that `b = lift a`. This is used by `ring` to construct an expression `b`
from the input expression `a`, and then run the usual ring algorithm on `b`. -/
/-
**Mathlib.Tactic.Ring.CSLiftVal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Ring
`。
形式化陈述：{α : Type u} → {β : outParam (Type u)} → [Mathlib.Tactic.Ring.CSLift α β] 
→ α → outParam β → Prop
参数：Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CSLiftVal a b` means that `b = lift a`. This is used by `ring` to construct an 
expression `b`
from the input expression `a`, and then run the usual ring algorithm on `b`.
-/
class CSLiftVal {α} {β : outParam (Type u)} [CSLift α β] (a : α) (b : outParam β) : Prop where
  /-- The output value `b` is equal to the lift of `a`. This can be supplied by the default
  instance which sets `b := lift a`, but `ring` will treat this as an atom so it is more useful
  when there are other instances which distribute addition or multiplication. -/
  eq : b = CSLift.lift a
/-
**Mathlib.Tactic.Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {α β} [CSLift α β] (a : α) : CSLiftVal a (CSLift.lift a) := ⟨rfl⟩
/-
**Mathlib.Tactic.Ring.of_lift** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：∀ {α β : Type u_2} [inst : Mathlib.Tactic.Ring.CSLift α β] {a b : α} {a' b
' : β}   [h1 : Mathlib.Tactic.Ring.CSLiftVal a a'] [h2 : Mathlib.Tactic.Ring.CSL
iftVal b b'], a' = b' → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.CSLift.inj`：∀ {α : Type u} {β : outParam (Type u)} [
self : Mathlib.Tactic.Ring.CSLift α β],   Function.Injective Mathlib.Tactic.Ring
.CSLift.lift
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.CSLiftVal.eq`：∀ {α : Type u} {β : outParam (Type u)}
 {inst : Mathlib.Tactic.Ring.CSLift α β} {a : α} {b : outParam β}   [self : Math
lib.Tactic.Ring.CSLift…
-/
theorem of_lift {α β} [inst : CSLift α β] {a b : α} {a' b' : β}
    [h1 : CSLiftVal a a'] [h2 : CSLiftVal b b'] (h : a' = b') : a = b :=
  inst.2 <| by rwa [← h1.1, ← h2.1]

open Lean Parser.Tactic Elab Command Elab.Tactic
/-
**Mathlib.Tactic.Ring.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：∀ {α : Sort u_2} {a b c : α}, a = c → b = c → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_eq {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b := by subst_vars; rfl

/--
This is a routine which is used to clean up the unsolved subgoal
of a failed `ring1` application. It is overridden in `Mathlib/Tactic/Ring/RingNF.lean`
to apply the `ring_nf` simp set to the goal.
-/
initialize ringCleanupRef : IO.Ref (Expr → MetaM Expr) ← IO.mkRef pure

/-- Frontend of `ring1`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
/-
**Mathlib.Tactic.Ring.proveEq** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Ring`。
形式化陈述：MVarId → Mathlib.Tactic.AtomM Unit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Frontend of `ring1`: attempt to close a goal `g`, assuming it is an equation of 
semirings.
-/
def proveEq (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "ring failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ←
    try Except.ok <$> synthInstanceQ q(CommSemiring $α)
    catch e => pure (.error e)
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let eq ← match sα with
  | .ok sα => ringCore sα e₁ e₂
  | .error e =>
    let β ← mkFreshExprMVarQ q(Type v)
    let e₁' ← mkFreshExprMVarQ q($β)
    let e₂' ← mkFreshExprMVarQ q($β)
    let (sβ, (pf : Q($e₁' = $e₂' → $e₁ = $e₂))) ← try
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
      let ⟨a, va, pa⟩ ← Common.eval rcℕ (ringCompute c) c e₁
      let ⟨b, vb, pb⟩ ← Common.eval rcℕ (ringCompute c) c e₂
      unless va.eq rcℕ (ringCompute c) vb do
        let g ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a = $b))
        throwError "ring failed, ring expressions not equal\n{g.mvarId!}"
      have : $a =Q $b := ⟨⟩
      return q(of_eq $pa $pb)

/--
`ring1` solves the goal when it is an equality in *commutative* (semi)rings,
allowing variables in the exponent.

This version of `ring` fails if the target is not an equality.

* `ring1!` uses a more aggressive reducibility setting to determine equality of atoms.
-/
elab (name := ring1) "ring1" tk:"!"? : tactic => liftMetaMAtMain fun g ↦ do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[tactic_alt ring1] macro "ring1!" : tactic => `(tactic| ring1 !)

end
end Mathlib.Tactic.Ring

