/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
module

public import Mathlib.Data.Nat.Cast.WithTop
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-!
# Solving equations about the Frobenius map on the field of fractions of `𝕎 k`

The goal of this file is to prove `WittVector.exists_frobenius_solution_fractionRing`,
which says that for an algebraically closed field `k` of characteristic `p` and `a, b` in the
field of fractions of Witt vectors over `k`,
there is a solution `b` to the equation `φ b * a = p ^ m * b`, where `φ` is the Frobenius map.

Most of this file builds up the equivalent theorem over `𝕎 k` directly,
moving to the field of fractions at the end.
See `WittVector.frobeniusRotation` and its specification.

The construction proceeds by recursively defining a sequence of coefficients as solutions to a
polynomial equation in `k`. We must define these as generic polynomials using Witt vector API
(`WittVector.wittMul`, `wittPolynomial`) to show that they satisfy the desired equation.

Preliminary work is done in the dependency `RingTheory.WittVector.MulCoeff`
to isolate the `n+1`st coefficients of `x` and `y` in the `n+1`st coefficient of `x*y`.

This construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].
We approximately follow an approach sketched on MathOverflow:
<https://mathoverflow.net/questions/62468/about-frobenius-of-witt-vectors>

The result is a dependency for the proof of `WittVector.isocrystal_classification`,
the classification of one-dimensional isocrystals over an algebraically closed field.
-/

@[expose] public section


noncomputable section

namespace WittVector

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

namespace RecursionMain

/-!

## The recursive case of the vector coefficients

The first coefficient of our solution vector is easy to define below.
In this section we focus on the recursive case.
The goal is to turn `WittVector.wittPolyProd n` into a univariate polynomial
whose variable represents the `n`th coefficient of `x` in `x * a`.

-/


section CommRing

variable {k : Type*} [CommRing k] [CharP k p]

open Polynomial

/-- The root of this polynomial determines the `n+1`st coefficient of our solution. -/
/-
**WittVector.RecursionMain.succNthDefiningPoly** 是 Mathlib 中的一个定义，位于命名空间 `WittVe
ctor.RecursionMain`。
形式化陈述：succNthDefiningPoly (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) : Poly
nomial k
参数：n : Nat；a₁ a₂ : 𝕎 k；bs : Fin (n + 1) -> k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The root of this polynomial determines the `n+1`st coefficient of our solution.
-/
def succNthDefiningPoly (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) → k) : Polynomial k :=
  X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1)) +
    C
      (a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) +
            nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) -
          a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) -
        nthRemainder p n bs (truncateFun (n + 1) a₂))
/-
**WittVector.RecursionMain.succNthDefiningPoly_degree** 是 Mathlib 中的一个定理，位于命名空间 
`WittVector.RecursionMain`。
形式化陈述：succNthDefiningPoly_degree [IsDomain k] (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin 
(n + 1) -> k) (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : (succNthDefining
Poly p n a₁ a₂ bs).degree = p
参数：n : Nat；a₁ a₂ : 𝕎 k；bs : Fin (n + 1) -> k；ha₁ : a₁.coeff 0 != 0；ha₂ : a₂.coef
f 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Polynomial.degree_pow`：degree_pow [Nontrivial R] (p : R[X]) (n : Nat) : 
degree (p ^ n) = n • degree p
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.degree_X`：degree_X : degree (X : R[X]) = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.degree_sub_eq_left_of_degree_lt`：degree_sub_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p - q) = degree p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `WittVector.RecursionMain.succNthDefiningPoly.eq_1`：∀ (p : ℕ) [hp : Fact 
(Nat.Prime p)] {k : Type u_1} [inst : CommRing k] [inst_1 : CharP k p] (n : ℕ)  
 (a₁ a₂ : WittVector p k) (bs : Fin (n …
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
-/
theorem succNthDefiningPoly_degree [IsDomain k] (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) → k)
    (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
    (succNthDefiningPoly p n a₁ a₂ bs).degree = p := by
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1))).degree = (p : WithBot ℕ) := by
    rw [degree_mul, degree_C]
    · simp
    · exact pow_ne_zero _ ha₁
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1))).degree =
      (p : WithBot ℕ) := by
    rw [degree_sub_eq_left_of_degree_lt, this]
    rw [this, degree_mul, degree_C, degree_X, add_zero]
    · exact mod_cast hp.out.one_lt
    · exact pow_ne_zero _ ha₂
  rw [succNthDefiningPoly, degree_add_eq_left_of_degree_lt, this]
  apply lt_of_le_of_lt degree_C_le
  rw [this]
  exact mod_cast hp.out.pos

end CommRing

section IsAlgClosed

variable {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]

/-
**WittVector.RecursionMain.root_exists** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.Rec
ursionMain`。
形式化陈述：root_exists (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coef
f 0 != 0) (ha₂ : a₂.coeff 0 != 0) : exists b : k, (succNthDefiningPoly p n a₁ a₂
 bs).IsRoot b
参数：n : Nat；a₁ a₂ : 𝕎 k；bs : Fin (n + 1) -> k；ha₁ : a₁.coeff 0 != 0；ha₂ : a₂.coef
f 0 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.exists_root`：exists_root [IsAlgClosed k] (p : k[X]) (hp : p.
degree != 0) : exists x, IsRoot p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.RecursionMain.succNthDefiningPoly_degree`：succNthDefiningPoly
_degree [IsDomain k] (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.c
oeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : (s…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem root_exists (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) → k) (ha₁ : a₁.coeff 0 ≠ 0)
    (ha₂ : a₂.coeff 0 ≠ 0) : ∃ b : k, (succNthDefiningPoly p n a₁ a₂ bs).IsRoot b :=
  IsAlgClosed.exists_root _ <| by
    simp only [succNthDefiningPoly_degree p n a₁ a₂ bs ha₁ ha₂, ne_eq, Nat.cast_eq_zero,
      hp.out.ne_zero, not_false_eq_true]

/-- This is the `n+1`st coefficient of our solution, projected from `root_exists`. -/
/-
**WittVector.RecursionMain.succNthVal** 是 Mathlib 中的一个定义，位于命名空间 `WittVector.Recu
rsionMain`。
形式化陈述：succNthVal (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff
 0 != 0) (ha₂ : a₂.coeff 0 != 0) : k
参数：n : Nat；a₁ a₂ : 𝕎 k；bs : Fin (n + 1) -> k；ha₁ : a₁.coeff 0 != 0；ha₂ : a₂.coef
f 0 != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.RecursionMain.root_exists`：root_exists (n : Nat) (a₁ a₂ : 𝕎 k
) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : exis
ts b : k, (succNthDefining…

--- 原说明 ---
This is the `n+1`st coefficient of our solution, projected from `root_exists`.
-/
def succNthVal (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) → k) (ha₁ : a₁.coeff 0 ≠ 0)
    (ha₂ : a₂.coeff 0 ≠ 0) : k :=
  Classical.choose (root_exists p n a₁ a₂ bs ha₁ ha₂)
/-
**WittVector.RecursionMain.succNthVal_spec** 是 Mathlib 中的一个定理，位于命名空间 `WittVector
.RecursionMain`。
形式化陈述：succNthVal_spec (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.
coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : (succNthDefiningPoly p n a₁ a₂ bs).IsRoo
t (succNthVal p n a₁ a₂ bs ha₁ ha₂)
参数：n : Nat；a₁ a₂ : 𝕎 k；bs : Fin (n + 1) -> k；ha₁ : a₁.coeff 0 != 0；ha₂ : a₂.coef
f 0 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `WittVector.RecursionMain.root_exists`：root_exists (n : Nat) (a₁ a₂ : 𝕎 k
) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : exis
ts b : k, (succNthDefining…
-/
theorem succNthVal_spec (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) → k) (ha₁ : a₁.coeff 0 ≠ 0)
    (ha₂ : a₂.coeff 0 ≠ 0) :
    (succNthDefiningPoly p n a₁ a₂ bs).IsRoot (succNthVal p n a₁ a₂ bs ha₁ ha₂) :=
  Classical.choose_spec (root_exists p n a₁ a₂ bs ha₁ ha₂)
/-
**WittVector.RecursionMain.succNthVal_spec'** 是 Mathlib 中的一个定理，位于命名空间 `WittVecto
r.RecursionMain`。
形式化陈述：succNthVal_spec' (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁
.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : succNthVal p n a₁ a₂ bs ha₁ ha₂ ^ p * a
₁.coeff 0 ^ p ^ (n + 1) + a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) + nthRemai
nder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) = succNthVal p n a₁ a₂ bs 
ha₁ ha₂ * a₂.coeff 0 ^ p ^ (n + 1) + a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) + nth
Remainder p n bs (truncateFun (n + 1) a₂)
参数：n : Nat；a₁ a₂ : 𝕎 k；bs : Fin (n + 1) -> k；ha₁ : a₁.coeff 0 != 0；ha₂ : a₂.coef
f 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `WittVector.RecursionMain.succNthVal_spec`：succNthVal_spec (n : Nat) (a₁ 
a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0
) : (succNthDefiningPoly p n a…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 52 条，此处仅展示前 30 条）
-/
theorem succNthVal_spec' (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) → k) (ha₁ : a₁.coeff 0 ≠ 0)
    (ha₂ : a₂.coeff 0 ≠ 0) :
    succNthVal p n a₁ a₂ bs ha₁ ha₂ ^ p * a₁.coeff 0 ^ p ^ (n + 1) +
          a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) +
        nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) =
      succNthVal p n a₁ a₂ bs ha₁ ha₂ * a₂.coeff 0 ^ p ^ (n + 1) +
          a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) +
        nthRemainder p n bs (truncateFun (n + 1) a₂) := by
  rw [← sub_eq_zero]
  have := succNthVal_spec p n a₁ a₂ bs ha₁ ha₂
  simp only [Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow, succNthDefiningPoly, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.IsRoot.def]
    at this
  convert! this using 1
  ring

end IsAlgClosed

end RecursionMain

namespace RecursionBase

variable {k : Type*} [Field k] [IsAlgClosed k]

/-
**WittVector.RecursionBase.solution_pow** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.Re
cursionBase`。
形式化陈述：solution_pow (a₁ a₂ : 𝕎 k) : exists x : k, x ^ (p - 1) = a₂.coeff 0 / a₁.c
oeff 0
参数：a₁ a₂ : 𝕎 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.exists_pow_nat_eq`：exists_pow_nat_eq [IsAlgClosed k] (x : k)
 {n : Nat} (hn : 0 < n) : exists z, z ^ n = x
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem solution_pow (a₁ a₂ : 𝕎 k) : ∃ x : k, x ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0 :=
  IsAlgClosed.exists_pow_nat_eq _ <| tsub_pos_of_lt hp.out.one_lt

/-- The base case (0th coefficient) of our solution vector. -/
/-
**WittVector.RecursionBase.solution** 是 Mathlib 中的一个定义，位于命名空间 `WittVector.Recurs
ionBase`。
形式化陈述：solution (a₁ a₂ : 𝕎 k) : k
参数：a₁ a₂ : 𝕎 k。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.RecursionBase.solution_pow`：solution_pow (a₁ a₂ : 𝕎 k) : exis
ts x : k, x ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0

--- 原说明 ---
The base case (0th coefficient) of our solution vector.
-/
def solution (a₁ a₂ : 𝕎 k) : k :=
  Classical.choose <| solution_pow p a₁ a₂
/-
**WittVector.RecursionBase.solution_spec** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.R
ecursionBase`。
形式化陈述：solution_spec (a₁ a₂ : 𝕎 k) : solution p a₁ a₂ ^ (p - 1) = a₂.coeff 0 / a₁
.coeff 0
参数：a₁ a₂ : 𝕎 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `WittVector.RecursionBase.solution_pow`：solution_pow (a₁ a₂ : 𝕎 k) : exis
ts x : k, x ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0
-/
theorem solution_spec (a₁ a₂ : 𝕎 k) : solution p a₁ a₂ ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0 :=
  Classical.choose_spec <| solution_pow p a₁ a₂
/-
**WittVector.RecursionBase.solution_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `WittVecto
r.RecursionBase`。
形式化陈述：solution_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 !
= 0) : solution p a₁ a₂ != 0
参数：ha₁ : a₁.coeff 0 != 0；ha₂ : a₂.coeff 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.RecursionBase.solution_spec`：solution_spec (a₁ a₂ : 𝕎 k) : so
lution p a₁ a₂ ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `div_eq_zero_iff`：div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.sub_ne_zero_of_lt`：∀ {a b : ℕ}, a < b → b - a ≠ 0
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem solution_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
    solution p a₁ a₂ ≠ 0 := by
  intro h
  have := solution_spec p a₁ a₂
  rw [h, zero_pow] at this
  · simpa [ha₁, ha₂] using _root_.div_eq_zero_iff.mp this.symm
  · exact Nat.sub_ne_zero_of_lt hp.out.one_lt
/-
**WittVector.RecursionBase.solution_spec'** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.
RecursionBase`。
形式化陈述：solution_spec' {a₁ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (a₂ : 𝕎 k) : solution p 
a₁ a₂ ^ p * a₁.coeff 0 = solution p a₁ a₂ * a₂.coeff 0
参数：ha₁ : a₁.coeff 0 != 0；a₂ : 𝕎 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.RecursionBase.solution_spec`：solution_spec (a₁ a₂ : 𝕎 k) : so
lution p a₁ a₂ ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem solution_spec' {a₁ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (a₂ : 𝕎 k) :
    solution p a₁ a₂ ^ p * a₁.coeff 0 = solution p a₁ a₂ * a₂.coeff 0 := by
  have := solution_spec p a₁ a₂
  have := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
  grind

end RecursionBase

open RecursionMain RecursionBase

section FrobeniusRotation

section IsAlgClosed

variable {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]

/-- Recursively defines the sequence of coefficients for `WittVector.frobeniusRotation`. -/
/-
**WittVector.frobeniusRotationCoeff** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：(p : ℕ) →   [hp : Fact (Nat.Prime p)] →     {k : Type u_1} →       [inst :
 Field k] →         [CharP k p] → [IsAlgClosed k] → {a₁ a₂ : WittVector p k} → a
₁.coeff 0 ≠ 0 → a₂.coeff 0 ≠ 0 → ℕ → k
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursively defines the sequence of coefficients for `WittVector.frobeniusRotati
on`.
-/
noncomputable def frobeniusRotationCoeff {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0)
    (ha₂ : a₂.coeff 0 ≠ 0) : ℕ → k
  | 0 => solution p a₁ a₂
  | n + 1 => succNthVal p n a₁ a₂ (fun i => frobeniusRotationCoeff ha₁ ha₂ i.val) ha₁ ha₂

/-- For nonzero `a₁` and `a₂`, `frobeniusRotation a₁ a₂` is a Witt vector that satisfies the
equation `frobenius (frobeniusRotation a₁ a₂) * a₁ = (frobeniusRotation a₁ a₂) * a₂`.
-/
/-
**WittVector.frobeniusRotation** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：frobeniusRotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 
!= 0) : 𝕎 k
参数：ha₁ : a₁.coeff 0 != 0；ha₂ : a₂.coeff 0 != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For nonzero `a₁` and `a₂`, `frobeniusRotation a₁ a₂` is a Witt vector that satis
fies the
equation `frobenius (frobeniusRotation a₁ a₂) * a₁ = (frobeniusRotation a₁ a₂) *
 a₂`.
-/
def frobeniusRotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : 𝕎 k :=
  WittVector.mk p (frobeniusRotationCoeff p ha₁ ha₂)
/-
**WittVector.frobeniusRotation_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：frobeniusRotation_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.
coeff 0 != 0) : frobeniusRotation p ha₁ ha₂ != 0
参数：ha₁ : a₁.coeff 0 != 0；ha₂ : a₂.coeff 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.RecursionBase.solution_nonzero`：solution_nonzero {a₁ a₂ : 𝕎 k
} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : solution p a₁ a₂ != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.frobeniusRotationCoeff.eq_1`：∀ (p : ℕ) [hp : Fact (Nat.Prime 
p)] {k : Type u_1} [inst : Field k] [inst_1 : CharP k p] [inst_2 : IsAlgClosed k
]   {a₁ a₂ : WittVector p k}…
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
-/
theorem frobeniusRotation_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
    frobeniusRotation p ha₁ ha₂ ≠ 0 := by
  intro h
  apply solution_nonzero p ha₁ ha₂
  simpa [← h, frobeniusRotation, frobeniusRotationCoeff] using WittVector.zero_coeff p k 0

set_option backward.isDefEq.respectTransparency.types false in
/-
**WittVector.frobenius_frobeniusRotation** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：frobenius_frobeniusRotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a
₂.coeff 0 != 0) : frobenius (frobeniusRotation p ha₁ ha₂) * a₁ = frobeniusRotati
on p ha₁ ha₂ * a₂
参数：ha₁ : a₁.coeff 0 != 0；ha₂ : a₂.coeff 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.mul_coeff_zero`：mul_coeff_zero (x y : 𝕎 R) : (x * y).coeff 0 
= x.coeff 0 * y.coeff 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WittVector.coeff_frobenius_charP`：coeff_frobenius_charP (x : 𝕎 R) (n : N
at) : coeff (frobenius x) n = x.coeff n ^ p
· 使用定理 `WittVector.frobeniusRotationCoeff.eq_1`：∀ (p : ℕ) [hp : Fact (Nat.Prime 
p)] {k : Type u_1} [inst : Field k] [inst_1 : CharP k p] [inst_2 : IsAlgClosed k
]   {a₁ a₂ : WittVector p k}…
· 使用定理 `WittVector.RecursionBase.solution_spec'`：solution_spec' {a₁ : 𝕎 k} (ha₁ 
: a₁.coeff 0 != 0) (a₂ : 𝕎 k) : solution p a₁ a₂ ^ p * a₁.coeff 0 = solution p a
₁ a₂ * a₂.coeff 0
· 使用定理 `WittVector.nthRemainder_spec`：nthRemainder_spec (n : Nat) (x y : 𝕎 k) : 
(x * y).coeff (n + 1) = x.coeff (n + 1) * y.coeff 0 ^ p ^ (n + 1) + y.coeff (n +
 1) * x.coeff 0 ^ …
· 使用定理 `WittVector.frobeniusRotationCoeff.eq_2`：∀ (p : ℕ) [hp : Fact (Nat.Prime 
p)] {k : Type u_1} [inst : Field k] [inst_1 : CharP k p] [inst_2 : IsAlgClosed k
]   {a₁ a₂ : WittVector p k}…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WittVector.RecursionMain.succNthVal_spec'`：succNthVal_spec' (n : Nat) (a
₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 !=
 0) : succNthVal p n a₁ a₂ bs h…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TruncatedWittVector.ext`：ext {x y : TruncatedWittVector p n R} (h : fora
ll i, x.coeff i = y.coeff i) : x = y
· 使用定理 `WittVector.coeff_truncateFun`：coeff_truncateFun (x : 𝕎 R) (i : Fin n) : 
(truncateFun n x).coeff i = x.coeff i
-/
theorem frobenius_frobeniusRotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
    frobenius (frobeniusRotation p ha₁ ha₂) * a₁ = frobeniusRotation p ha₁ ha₂ * a₂ := by
  ext n
  rcases n with - | n
  · simp only [WittVector.mul_coeff_zero, WittVector.coeff_frobenius_charP, frobeniusRotation,
      coeff_mk, frobeniusRotationCoeff]
    exact solution_spec' _ ha₁ _
  · simp only [nthRemainder_spec, WittVector.coeff_frobenius_charP,
      frobeniusRotation, coeff_mk, frobeniusRotationCoeff]
    have :=
      succNthVal_spec' p n a₁ a₂ (fun i : Fin (n + 1) => frobeniusRotationCoeff p ha₁ ha₂ i.val)
        ha₁ ha₂
    simp only [frobeniusRotationCoeff, Fin.val_zero] at this
    convert! this using 3; clear this
    apply TruncatedWittVector.ext
    intro i
    simp only [WittVector.coeff_truncateFun, WittVector.coeff_frobenius_charP]
    rfl

local notation "φ" => IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)

-- Non-terminal simp, used to be field_simp
set_option linter.flexible false in
-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-
**WittVector.exists_frobenius_solution_fractionRing_aux** 是 Mathlib 中的一个定理，位于命名空
间 `WittVector`。
形式化陈述：exists_frobenius_solution_fractionRing_aux (m n : Nat) (r' q' : 𝕎 k) (hr' 
: r'.coeff 0 != 0) (hq' : q'.coeff 0 != 0) (hq : (p : 𝕎 k) ^ n * q' in nonZeroDi
visors (𝕎 k)) : let b : 𝕎 k
参数：m n : Nat；r' q' : 𝕎 k；hr' : r'.coeff 0 != 0；hq' : q'.coeff 0 != 0；hq : (p : 𝕎
 k) ^ n * q' in nonZeroDivisors (𝕎 k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `WittVector.frobenius_frobeniusRotation`：frobenius_frobeniusRotation {a₁ 
a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : frobenius (frobenius
Rotation p ha₁ ha₂) * a₁ = f…
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 101 条，此处仅展示前 30 条）
-/
theorem exists_frobenius_solution_fractionRing_aux (m n : ℕ) (r' q' : 𝕎 k) (hr' : r'.coeff 0 ≠ 0)
    (hq' : q'.coeff 0 ≠ 0) (hq : (p : 𝕎 k) ^ n * q' ∈ nonZeroDivisors (𝕎 k)) :
    let b : 𝕎 k := frobeniusRotation p hr' hq'
    IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)
          (algebraMap (𝕎 k) (FractionRing (𝕎 k)) b) *
        Localization.mk ((p : 𝕎 k) ^ m * r') ⟨(p : 𝕎 k) ^ n * q', hq⟩ =
      (p : Localization (nonZeroDivisors (𝕎 k))) ^ (m - n : ℤ) *
        algebraMap (𝕎 k) (FractionRing (𝕎 k)) b := by
  intro b
  have key : WittVector.frobenius b * r' = q' * b := by
    linear_combination frobenius_frobeniusRotation p hr' hq'
  have hq'' : algebraMap (𝕎 k) (FractionRing (𝕎 k)) q' ≠ 0 := by
    have hq''' : q' ≠ 0 := fun h => hq' (by simp [h])
    simpa only [Ne, map_zero] using
      (IsFractionRing.injective (𝕎 k) (FractionRing (𝕎 k))).ne hq'''
  rw [zpow_sub₀ (FractionRing.p_nonzero p k)]
  simp [field, FractionRing.p_nonzero p k]
  convert! congr_arg (fun x => algebraMap (𝕎 k) (FractionRing (𝕎 k)) x) key using 1
  · simp only [map_mul]
  · simp only [map_mul]
/-
**WittVector.exists_frobenius_solution_fractionRing** 是 Mathlib 中的一个定理，位于命名空间 `W
ittVector`。
形式化陈述：exists_frobenius_solution_fractionRing {a : FractionRing (𝕎 k)} (ha : a !=
 0) : existsᵉ (b != 0) (m : Int), φ b * a = (p : FractionRing (𝕎 k)) ^ m * b
参数：𝕎 k；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.induction_on`：induction_on {p : Localization S -> Prop} (x)
 (H : forall y : M × S, p (mk y.1 y.2)) : p x
· 使用定理 `IsAlgClosed.perfectField`：∀ (k : Type u) [inst : Field k] [IsAlgClosed k
], PerfectField k
· 使用定理 `WittVector.instNontrivial`：∀ {p : ℕ} {R : Type u_1} [CommRing R] [Fact (
Nat.Prime p)] [Nontrivial R], Nontrivial (WittVector p R)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `WittVector.instNoZeroDivisorsOfCharP`：∀ {p : ℕ} {R : Type u_1} [hp : Fac
t (Nat.Prime p)] [inst : CommRing R] [CharP R p] [NoZeroDivisors R],   NoZeroDiv
isors (WittVector p R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `FractionRing.mk_eq_div`：mk_eq_div {r s} : (Localization.mk r s : Fractio
nRing A) = (algebraMap _ _ r / algebraMap A _ s : FractionRing A)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WittVector.exists_eq_pow_p_mul`：exists_eq_pow_p_mul (a : 𝕎 k) (ha : a !=
 0) : exists (m : Nat) (b : 𝕎 k), b.coeff 0 != 0 ∧ a = (p : 𝕎 k) ^ m * b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `WittVector.frobeniusRotation_nonzero`：frobeniusRotation_nonzero {a₁ a₂ :
 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : frobeniusRotation p ha₁ 
ha₂ != 0
· 使用定理 `WittVector.exists_frobenius_solution_fractionRing_aux`：exists_frobenius_
solution_fractionRing_aux (m n : Nat) (r' q' : 𝕎 k) (hr' : r'.coeff 0 != 0) (hq'
 : q'.coeff 0 != 0) (hq : (p : 𝕎 k) ^ n * q…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_frobenius_solution_fractionRing {a : FractionRing (𝕎 k)} (ha : a ≠ 0) :
    ∃ᵉ (b ≠ 0) (m : ℤ), φ b * a = (p : FractionRing (𝕎 k)) ^ m * b := by
  revert ha
  refine Localization.induction_on a ?_
  rintro ⟨r, q, hq⟩ hrq
  have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 hq
  have hr0 : r ≠ 0 := fun h => hrq (by simp [h])
  obtain ⟨m, r', hr', rfl⟩ := exists_eq_pow_p_mul r hr0
  obtain ⟨n, q', hq', rfl⟩ := exists_eq_pow_p_mul q hq0
  let b := frobeniusRotation p hr' hq'
  refine ⟨algebraMap (𝕎 k) (FractionRing (𝕎 k)) b, ?_, m - n, ?_⟩
  · simpa only [map_zero] using
      (IsFractionRing.injective (WittVector p k) (FractionRing (WittVector p k))).ne
        (frobeniusRotation_nonzero p hr' hq')
  exact exists_frobenius_solution_fractionRing_aux p m n r' q' hr' hq' hq

end IsAlgClosed

end FrobeniusRotation

end WittVector

