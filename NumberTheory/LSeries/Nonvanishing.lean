/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Positivity

/-!
# The L-function of a Dirichlet character does not vanish on Re(s) ≥ 1

The main result in this file is `DirichletCharacter.LFunction_ne_zero_of_one_le_re`:
if `χ` is a Dirichlet character, `s ∈ ℂ` with `1 ≤ s.re`, and either `χ` is nontrivial or `s ≠ 1`,
then the L-function of `χ` does not vanish at `s`.

As a consequence, we have the corresponding statement for the Riemann ζ function:
`riemannZeta_ne_zero_of_one_le_re` (which does not require `s ≠ 1`, since the junk value at `s = 1`
happens to be non-zero).

These results are prerequisites for the **Prime Number Theorem** and
**Dirichlet's Theorem** on primes in arithmetic progressions.

## Outline of proofs

We split into two cases: first, the special case of (non-trivial) quadratic characters at `s = 1`;
then the remaining case when either `s ≠ 1` or `χ ^ 2 ≠ 1`.

The first case is handled using a positivity argument applied to the series `L χ s * ζ s`: we show
that this function has non-negative Dirichlet coefficients, is strictly positive for `s ≫ 0`, but
vanishes at `s = -2`, so it must have a pole somewhere in between.

The second case is dealt with using the product
`L(χ^0, 1 + x)^3 L(χ, 1 + x + I * y)^4 L(χ^2, 1 + x + 2 * I * y)`, which
we show has absolute value `≥ 1` for all positive `x` and real `y`; if `L(χ, 1 + I * y) = 0` then
this product would have to tend to 0 as `x → 0`, which is a contradiction.
-/

@[expose] public section

/- NB: Many lemmas (and some defs) in this file are private, since they concern properties of
hypothetical objects which we eventually deduce cannot exist. We have only made public the lemmas
whose hypotheses do not turn out to be contradictory.
-/

open Complex Asymptotics Topology Filter
open ArithmeticFunction hiding log

-- We use the ordering on `ℂ` given by comparing real parts for fixed imaginary part
open scoped ComplexOrder

variable {N : ℕ}

namespace DirichletCharacter

section quadratic

/-!
### Convolution of a Dirichlet character with ζ

We define `DirichletCharacter.zetaMul χ` to be the arithmetic function obtained by
taking the product (as arithmetic functions = Dirichlet convolution) of the
arithmetic function `ζ` with `χ`.

We then show that for a quadratic character `χ`, this arithmetic function is multiplicative
and takes nonnegative real values.
-/

/-- The complex-valued arithmetic function that is the convolution of the constant
function `1` with `χ`. -/
/-
**DirichletCharacter.zetaMul** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：zetaMul (χ : DirichletCharacter Complex N) : ArithmeticFunction Complex
参数：χ : DirichletCharacter Complex N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complex-valued arithmetic function that is the convolution of the constant
function `1` with `χ`.
-/
noncomputable def zetaMul (χ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  .zeta * toArithmeticFunction (χ ·)

/-- The arithmetic function `zetaMul χ` is multiplicative. -/
/-
**DirichletCharacter.isMultiplicative_zetaMul** 是 Mathlib 中的一个引理，位于命名空间 `Dirichl
etCharacter`。
形式化陈述：isMultiplicative_zetaMul (χ : DirichletCharacter Complex N) : χ.zetaMul.Is
Multiplicative
参数：χ : DirichletCharacter Complex N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.IsMultiplicative.mul`：mul [CommSemiring R] {f g : Ari
thmeticFunction R} (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : IsMulti
plicative (f * g)
· 使用定理 `ArithmeticFunction.IsMultiplicative.natCast`：natCast {f : ArithmeticFunc
tion Nat} [Semiring R] (h : f.IsMultiplicative) : IsMultiplicative (f : Arithmet
icFunction R)
· 使用定理 `ArithmeticFunction.isMultiplicative_zeta`：isMultiplicative_zeta : IsMult
iplicative ζ
· 使用引理 `DirichletCharacter.isMultiplicative_toArithmeticFunction`：isMultiplicati
ve_toArithmeticFunction {N : Nat} {R : Type*} [CommMonoidWithZero R] (χ : Dirich
letCharacter R N) : (toArithmeticFunction (χ ·…

--- 原说明 ---
The arithmetic function `zetaMul χ` is multiplicative.
-/
lemma isMultiplicative_zetaMul (χ : DirichletCharacter ℂ N) : χ.zetaMul.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul <| isMultiplicative_toArithmeticFunction χ
/-
**DirichletCharacter.LSeriesSummable_zetaMul** 是 Mathlib 中的一个引理，位于命名空间 `Dirichle
tCharacter`。
形式化陈述：LSeriesSummable_zetaMul (χ : DirichletCharacter Complex N) {s : Complex} (
hs : 1 < s.re) : LSeriesSummable χ.zetaMul s
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ArithmeticFunction.LSeriesSummable_mul`：LSeriesSummable_mul {f g : Arith
meticFunction Complex} {s : Complex} (hf : LSeriesSummable ↗f s) (hg : LSeriesSu
mmable ↗g s) : LSeriesSummab…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.LSeriesSummable_zeta_iff`：LSeriesSummable_zeta_iff {s
 : Complex} : LSeriesSummable (ζ ·) s ↔ 1 < s.re
· 使用定理 `LSeriesSummable_of_bounded_of_one_lt_re`：LSeriesSummable_of_bounded_of_o
ne_lt_re {f : Nat -> Complex} {m : Real} (h : forall n != 0, ‖f n‖ <= m) {s : Co
mplex} (hs : 1 < s.re) : LSer…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `DirichletCharacter.norm_le_one`：norm_le_one (a : ZMod n) : ‖χ a‖ <= 1
-/
lemma LSeriesSummable_zetaMul (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable χ.zetaMul s := by
  refine ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zeta_iff.mpr hs) <|
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn ↦ ?_) hs
  simpa only [toArithmeticFunction, coe_mk, hn, ↓reduceIte]
  using norm_le_one χ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**DirichletCharacter.zetaMul_prime_pow_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Dirichl
etCharacter`。
形式化陈述：zetaMul_prime_pow_nonneg {χ : DirichletCharacter Complex N} (hχ : χ ^ 2 = 
1) {p : Nat} (hp : p.Prime) (k : Nat) : 0 <= zetaMul χ (p ^ k)
参数：hχ : χ ^ 2 = 1；hp : p.Prime；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `ArithmeticFunction.coe_zeta_mul_apply`：coe_zeta_mul_apply [Semiring R] {
f : ArithmeticFunction R} {x : Nat} : (ζ * f) x = ∑ i in divisors x, f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.sum_divisors_prime_pow`：∀ {α : Type u_1} [inst : AddCommMonoid α] {k
 p : ℕ} {f : ℕ → α},   Nat.Prime p → ∑ x ∈ (p ^ k).divisors, f x = ∑ x ∈ Finset.
range (k + 1), f…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MulChar.isQuadratic_iff_sq_eq_one`：isQuadratic_iff_sq_eq_one {M R : Type
*} [CommMonoid M] [CommRing R] [NoZeroDivisors R] [Nontrivial R] {χ : MulChar M 
R} : IsQuadratic χ ↔ χ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 37 条，此处仅展示前 30 条）
-/
lemma zetaMul_prime_pow_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    0 ≤ zetaMul χ (p ^ k) := by
  simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

/-- `zetaMul χ` takes nonnegative real values when `χ` is a quadratic character. -/
/-
**DirichletCharacter.zetaMul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacte
r`。
形式化陈述：zetaMul_nonneg {χ : DirichletCharacter Complex N} (hχ : χ ^ 2 = 1) (n : Na
t) : 0 <= zetaMul χ n
参数：hχ : χ ^ 2 = 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.IsMultiplicative.multiplicative_factorization`：multip
licative_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R) (hf : f
.IsMultiplicative) {n : Nat} (hn : n != 0) : f n = n.f…
· 使用引理 `DirichletCharacter.isMultiplicative_zetaMul`：isMultiplicative_zetaMul (χ
 : DirichletCharacter Complex N) : χ.zetaMul.IsMultiplicative
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用引理 `DirichletCharacter.zetaMul_prime_pow_nonneg`：zetaMul_prime_pow_nonneg {χ
 : DirichletCharacter Complex N} (hχ : χ ^ 2 = 1) {p : Nat} (hp : p.Prime) (k : 
Nat) : 0 <= zetaMul χ (p ^ k)
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime

--- 原说明 ---
`zetaMul χ` takes nonnegative real values when `χ` is a quadratic character.
-/
lemma zetaMul_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [χ.isMultiplicative_zetaMul.multiplicative_factorization _ hn] using!
      Finset.prod_nonneg
        fun p hp ↦ zetaMul_prime_pow_nonneg hχ (Nat.prime_of_mem_primeFactors hp) _

/-
### "Bad" Dirichlet characters

Our goal is to show that `L(χ, 1) ≠ 0` when `χ` is a (nontrivial) quadratic Dirichlet character.
To do that, we package the contradictory properties in a (private) structure
`DirichletCharacter.BadChar` and derive further statements eventually leading to a contradiction.

This entire section is private.
-/

/-- The object we're trying to show doesn't exist: A nontrivial quadratic Dirichlet character
whose L-function vanishes at `s = 1`. -/
/-
**DirichletCharacter.BadChar** 是 Mathlib 中的一个结构，位于命名空间 `DirichletCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object we're trying to show doesn't exist: A nontrivial quadratic Dirichlet 
character
whose L-function vanishes at `s = 1`.
-/
private structure BadChar (N : ℕ) [NeZero N] where
  /-- The character we want to show cannot exist. -/
  χ : DirichletCharacter ℂ N
  χ_ne : χ ≠ 1
  χ_sq : χ ^ 2 = 1
  hχ : χ.LFunction 1 = 0

variable [NeZero N]

namespace BadChar

/-- The product of the Riemann zeta function with the L-function of `B.χ`.
We will show that `B.F (-2) = 0` but also that `B.F (-2)` must be positive,
giving the desired contradiction. -/
private noncomputable
/-
**DirichletCharacter.BadChar.F** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter.Bad
Char`。
形式化陈述：F (B : BadChar N) : Complex -> Complex
参数：B : BadChar N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def F (B : BadChar N) : ℂ → ℂ :=
  Function.update (fun s : ℂ ↦ riemannZeta s * LFunction B.χ s) 1 (deriv (LFunction B.χ) 1)
/-
**DirichletCharacter.BadChar.F_differentiableAt_of_ne** 是 Mathlib 中的一个引理，位于命名空间 
`DirichletCharacter.BadChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma F_differentiableAt_of_ne (B : BadChar N) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ B.F s := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · exact (differentiableAt_riemannZeta hs).mul <| differentiableAt_LFunction B.χ s (.inl hs)
  · filter_upwards [eventually_ne_nhds hs] with t ht using Function.update_of_ne ht ..

/-- `B.F` agrees with the L-series of `zetaMul χ` on `1 < s.re`. -/
/-
**DirichletCharacter.BadChar.F_eq_LSeries** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCh
aracter.BadChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`B.F` agrees with the L-series of `zetaMul χ` on `1 < s.re`.
-/
private lemma F_eq_LSeries (B : BadChar N) {s : ℂ} (hs : 1 < s.re) :
    B.F s = LSeries B.χ.zetaMul s := by
  rw [F, zetaMul, ← coe_mul, LSeries_convolution']
  · have hs' : s ≠ 1 := fun h ↦ by simp only [h, one_re, lt_self_iff_false] at hs
    simp only [ne_eq, hs', not_false_eq_true, Function.update_of_ne, B.χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr B.χ.apply_eq_toArithmeticFunction_apply s
  -- summability side goals from `LSeries_convolution'`
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (B.χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re B.χ hs

/-- If `χ` is a bad character, then `F` is an entire function. -/
/-
**DirichletCharacter.BadChar.F_differentiable** 是 Mathlib 中的一个引理，位于命名空间 `Dirichl
etCharacter.BadChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `χ` is a bad character, then `F` is an entire function.
-/
private lemma F_differentiable (B : BadChar N) : Differentiable ℂ B.F := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact B.F_differentiableAt_of_ne hs
  -- now need to deal with `s = 1`
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact B.F_differentiableAt_of_ne ht
  -- now reduced to showing *continuity* at s = 1
  let G := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
  let H := Function.update (fun s ↦ (B.χ.LFunction s - B.χ.LFunction 1) / (s - 1)) 1
    (deriv B.χ.LFunction 1)
  have : B.F = G * H := by
    ext1 t
    rcases eq_or_ne t 1 with rfl | ht
    · simp only [F, G, H, Pi.mul_apply, one_mul, Function.update_self]
    · simp only [F, G, H, Function.update_of_ne ht, mul_comm _ (riemannZeta _), B.hχ, sub_zero,
      Pi.mul_apply, mul_assoc, mul_div_cancel₀ _ (sub_ne_zero.mpr ht)]
  rw [this]
  apply ContinuousAt.mul
  · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
  · exact (B.χ.differentiableAt_LFunction 1 (.inr B.χ_ne)).hasDerivAt.continuousAt_div

/-- The trivial zero at `s = -2` of the zeta function gives that `F (-2) = 0`.
This is used later to obtain a contradiction. -/
/-
**DirichletCharacter.BadChar.F_neg_two** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter.BadChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial zero at `s = -2` of the zeta function gives that `F (-2) = 0`.
This is used later to obtain a contradiction.
-/
private lemma F_neg_two (B : BadChar N) : B.F (-2 : ℝ) = 0 := by
  have := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at this
  rw [F, ofReal_neg, ofReal_ofNat, Function.update_of_ne (mod_cast (by lia : (-2 : ℤ) ≠ 1)),
    this, zero_mul]

end BadChar

/-- If `χ` is a nontrivial quadratic Dirichlet character, then `L(χ, 1) ≠ 0`. This is private
since it is later superseded by `LFunction_apply_one_ne_zero`. -/
/-
**DirichletCharacter.LFunction_apply_one_ne_zero_of_quadratic** 是 Mathlib 中的一个定理
，位于命名空间 `DirichletCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `χ` is a nontrivial quadratic Dirichlet character, then `L(χ, 1) ≠ 0`. This i
s private
since it is later superseded by `LFunction_apply_one_ne_zero`.
-/
private theorem LFunction_apply_one_ne_zero_of_quadratic {χ : DirichletCharacter ℂ N}
    (hχ : χ ^ 2 = 1) (χ_ne : χ ≠ 1) :
    χ.LFunction 1 ≠ 0 := by
  intro hL
  -- construct a "bad character" and put together a contradiction.
  let B : BadChar N := { χ := χ, χ_sq := hχ, hχ := hL, χ_ne := χ_ne }
  refine B.F_neg_two.not_gt ?_
  refine ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn (zetaMul_nonneg hχ)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one) B.F_differentiable ?_
    (fun _ ↦ B.F_eq_LSeries) _
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    fun _ a ↦ χ.LSeriesSummable_zetaMul a

end quadratic

section nonvanishing

variable (χ : DirichletCharacter ℂ N)

-- This is the key positivity lemma that is used to show that the L-function
-- of a Dirichlet character `χ` does not vanish for `s.re ≥ 1` (unless `χ^2 = 1` and `s = 1`).
/-
**DirichletCharacter.re_log_comb_nonneg'** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCha
racter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma re_log_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
      0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

-- This is the version of the technical positivity lemma for logarithms of Euler factors.
/-
**DirichletCharacter.re_log_comb_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChar
acter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma re_log_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    0 ≤ 3 * (-log (1 - (1 : DirichletCharacter ℂ N) n * n ^ (-x : ℂ))).re +
          4 * (-log (1 - χ n * n ^ (-(x + I * y)))).re +
          (-log (1 - (χ n ^ 2) * n ^ (-(x + 2 * I * y)))).re := by
  by_cases hn' : IsUnit (n : ZMod N)
  · have hn : (n : ℝ) ^ (-x) < 1 := by
      rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
      exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
    have hz : ‖χ n * (n : ℂ) ^ (-(I * y))‖ = 1 := by
      rw [norm_mul, ← hn'.unit_spec, DirichletCharacter.unit_norm_eq_one χ hn'.unit,
        ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (mod_cast by lia)]
      simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
        neg_zero, Real.rpow_zero, one_mul]
    rw [MulChar.one_apply hn', one_mul]
    convert! re_log_comb_nonneg' (by positivity) hn hz using 6
    · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
    · congr 2
      rw [neg_add, cpow_add _ _ <| mod_cast by lia, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, mul_left_comm]
    · rw [neg_add, cpow_add _ _ <| mod_cast by lia, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
        mul_left_comm]
  · simp only [MulChar.map_nonunit _ hn', zero_mul, sub_zero, log_one, neg_zero, zero_re, mul_zero,
      neg_add_rev, add_zero, pow_two, le_refl]

/-- The logarithms of the Euler factors of a Dirichlet L-series form a summable sequence. -/
/-
**DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow** 是 Mathlib 中的一个引理，
位于命名空间 `DirichletCharacter`。
形式化陈述：summable_neg_log_one_sub_mul_prime_cpow {s : Complex} (hs : 1 < s.re) : Su
mmable fun p : Nat.Primes => -log (1 - χ p * (p : Complex) ^ (-s))
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Complex.norm_natCast_cpow_of_re_ne_zero`：norm_natCast_cpow_of_re_ne_zero
 (n : Nat) {s : Complex} (hs : s.re != 0) : ‖(n : Complex) ^ s‖ = (n : Real) ^ (
s.re)
· 使用引理 `Complex.re_neg_ne_zero_of_one_lt_re`：re_neg_ne_zero_of_one_lt_re {s : Co
mplex} (hs : 1 < s.re) : (-s).re != 0
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `DirichletCharacter.norm_le_one`：norm_le_one (a : ZMod n) : ‖χ a‖ <= 1
· 使用定理 `Summable.neg`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [i
nst : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] 
{f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Summable.clog_one_sub`：Summable.clog_one_sub {α : Type*} {f : α -> Compl
ex} (hsum : Summable f) : Summable fun n => log (1 - f n)
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Primes.summable_rpow`：Nat.Primes.summable_rpow {r : Real} : Summable
 (fun p : Nat.Primes => (p : Real) ^ r) ↔ r < -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The logarithms of the Euler factors of a Dirichlet L-series form a summable sequ
ence.
-/
lemma summable_neg_log_one_sub_mul_prime_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ -log (1 - χ p * (p : ℂ) ^ (-s)) := by
  have (p : Nat.Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s).re := by
    simpa only [norm_mul, norm_natCast_cpow_of_re_ne_zero _ <| re_neg_ne_zero_of_one_lt_re hs]
      using mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le (fun _ ↦ norm_nonneg _) this
    |>.of_norm.clog_one_sub.neg
  simp only [neg_re, neg_lt_neg_iff, hs]
/-
**DirichletCharacter.one_lt_re_one_add** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma one_lt_re_one_add {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 < (1 + x : ℂ).re ∧ 1 < (1 + x + I * y).re ∧ 1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]

open scoped LSeries.notation in
/-- For positive `x` and nonzero `y` and a Dirichlet character `χ` we have
`|L(χ^0, 1 + x)^3 * L(χ, 1 + x + I * y)^4 * L(χ^2, 1 + x + 2 * I * y)| ≥ 1`. -/
/-
**DirichletCharacter.norm_LSeries_product_ge_one** 是 Mathlib 中的一个引理，位于命名空间 `Diri
chletCharacter`。
形式化陈述：norm_LSeries_product_ge_one {x : Real} (hx : 0 < x) (y : Real) : ‖L ↗(1 : 
DirichletCharacter Complex N) (1 + x) ^ 3 * L ↗χ (1 + x + I * y) ^ 4 * L ↗(χ ^ 2
 :) (1 + x + 2 * I * y)‖ >= 1
参数：hx : 0 < x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.Nonvanishing.0.DirichletCharacter.
one_lt_re_one_add`：∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 1 < (1 + ↑x).re ∧ 1 < (1 + ↑x +
 Complex.I * ↑y).re ∧ 1 < (1 + ↑x + 2 * Complex.I * ↑y).re
· 使用引理 `DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow`：summable_neg
_log_one_sub_mul_prime_cpow {s : Complex} (hs : 1 < s.re) : Summable fun p : Nat
.Primes => -log (1 - χ p * (p : Complex) ^ (-s))
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `Complex.hasSum_re`：∀ {α : Type u_1} {L : SummationFilter α} {f : α → ℂ} 
{x : ℂ}, HasSum f x L → HasSum (fun x => (f x).re) x.re L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirichletCharacter.LSeries_eulerProduct_exp_log`：DirichletCharacter.LSer
ies_eulerProduct_exp_log {N : Nat} (χ : DirichletCharacter Complex N) {s : Compl
ex} (hs : 1 < s.re) : exp (∑' p : Nat…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Complex.re_tsum`：∀ {α : Type u_1} {L : SummationFilter α} [L.NeBot] {f :
 α → ℂ},   Summable f L → (∑'[L] (a : α), f a).re = ∑'[L] (a : α), (f a).re
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `tsum_mul_left`：tsum_mul_left [T2Space α] : ∑'[L] x, a * f x = a * ∑'[L] 
x, f x
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Summable.tsum_add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid
 α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2Spa
ce α] […
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Summable.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [Continuous
Ad…
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
For positive `x` and nonzero `y` and a Dirichlet character `χ` we have
`|L(χ^0, 1 + x)^3 * L(χ, 1 + x + I * y)^4 * L(χ^2, 1 + x + 2 * I * y)| ≥ 1`.
-/
lemma norm_LSeries_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖L ↗(1 : DirichletCharacter ℂ N) (1 + x) ^ 3 * L ↗χ (1 + x + I * y) ^ 4 *
      L ↗(χ ^ 2 :) (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have H₀ := summable_neg_log_one_sub_mul_prime_cpow (N := N) 1 h₀
  have H₁ := summable_neg_log_one_sub_mul_prime_cpow χ h₁
  have H₂ := summable_neg_log_one_sub_mul_prime_cpow (χ ^ 2) h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← LSeries_eulerProduct_exp_log _ h₀, ← LSeries_eulerProduct_exp_log χ h₁,
    ← LSeries_eulerProduct_exp_log _ h₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  simpa only [neg_add_rev, neg_re, mul_neg, χ.pow_apply' two_ne_zero, ge_iff_le, add_re, one_re,
    ofReal_re, ofReal_add, ofReal_one] using
      tsum_nonneg fun (p : Nat.Primes) ↦ χ.re_log_comb_nonneg p.prop.two_le h₀ y

variable [NeZero N]

/-- A variant of `DirichletCharacter.norm_LSeries_product_ge_one` in terms of the L-functions. -/
/-
**DirichletCharacter.norm_LFunction_product_ge_one** 是 Mathlib 中的一个引理，位于命名空间 `Di
richletCharacter`。
形式化陈述：norm_LFunction_product_ge_one {x : Real} (hx : 0 < x) (y : Real) : ‖LFunct
ionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * y) ^ 4 * LFunction (χ ^ 2) 
(1 + x + 2 * I * y)‖ >= 1
参数：hx : 0 < x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.Nonvanishing.0.DirichletCharacter.
one_lt_re_one_add`：∀ {x : ℝ}, 0 < x → ∀ (y : ℝ), 1 < (1 + ↑x).re ∧ 1 < (1 + ↑x +
 Complex.I * ↑y).re ∧ 1 < (1 + ↑x + 2 * Complex.I * ↑y).re
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirichletCharacter.LFunctionTrivChar.eq_1`：∀ (N : ℕ) [inst : NeZero N], 
DirichletCharacter.LFunctionTrivChar N = DirichletCharacter.LFunction 1
· 使用引理 `DirichletCharacter.LFunction_eq_LSeries`：LFunction_eq_LSeries (χ : Diric
hletCharacter Complex N) {s : Complex} (hs : 1 < re s) : LFunction χ s = LSeries
 (χ ·) s
· 使用引理 `DirichletCharacter.norm_LSeries_product_ge_one`：norm_LSeries_product_ge_
one {x : Real} (hx : 0 < x) (y : Real) : ‖L ↗(1 : DirichletCharacter Complex N) 
(1 + x) ^ 3 * L ↗χ (1 + x + I * y) ^…

--- 原说明 ---
A variant of `DirichletCharacter.norm_LSeries_product_ge_one` in terms of the L-
functions.
-/
lemma norm_LFunction_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * y) ^ 4 *
      LFunction (χ ^ 2) (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  rw [LFunctionTrivChar, DirichletCharacter.LFunction_eq_LSeries 1 h₀,
    χ.LFunction_eq_LSeries h₁, (χ ^ 2).LFunction_eq_LSeries h₂]
  exact norm_LSeries_product_ge_one χ hx y
/-
**DirichletCharacter.LFunctionTrivChar_isBigO_near_one_horizontal** 是 Mathlib 中的
一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：LFunctionTrivChar_isBigO_near_one_horizontal : (fun x : Real => LFunctionT
rivChar N (1 + x)) =O[𝓝[>] 0] fun x => (1 : Complex) / x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `DirichletCharacter.LFunctionTrivChar_residue_one`：LFunctionTrivChar_resi
due_one : Tendsto (fun s => (s - 1) * LFunctionTrivChar N s) (𝓝[!=] 1) (𝓝 <| ∏ p
 in N.primeFactors, (1 - (p : Complex)…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Homeomorph.map_punctured_nhds_eq`：map_punctured_nhds_eq (h : X ≃ₜ Y) (x 
: X) : map h (𝓝[!=] x) = 𝓝[!=] (h x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Asymptotics.isBigO_mul_iff_isBigO_div`：isBigO_mul_iff_isBigO_div {f g h 
: α -> 𝕜} (hf : forallᶠ x in l, f x != 0) : (fun x => f x * g x) =O[l] h ↔ g =O[
l] (fun x => h x / f x)
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.Tendsto.isBigO_one`：∀ {α : Type u_1} (F : Type u_4) {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {f' : α → E'}   {l : Fil
ter α} [inst_2 …
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用引理 `Complex.isBigO_comp_ofReal_nhds_ne`：isBigO_comp_ofReal_nhds_ne {f g : Co
mplex -> Complex} {x : Real} (h : f =O[𝓝[!=] (x : Complex)] g) : (fun y : Real =
> f y) =O[𝓝[!=] x] (fun …
· 使用定理 `nhdsGT_le_nhdsNE`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 :
 Preorder α] (a : α), nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a {a}ᶜ
-/
lemma LFunctionTrivChar_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ LFunctionTrivChar N (1 + x)) =O[𝓝[>] 0] fun x ↦ (1 : ℂ) / x := by
  have : (fun w : ℂ ↦ LFunctionTrivChar N (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * LFunctionTrivChar N (1 + w)) (𝓝[≠] 0)
        (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
      convert! (LFunctionTrivChar_residue_one (N := N)).comp (f := fun w ↦ 1 + w) ?_ using 1
      · simp only [Function.comp_def, add_sub_cancel_left]
      · simpa only [tendsto_iff_comap, Homeomorph.coe_addLeft, add_zero, map_le_iff_le_comap] using
          ((Homeomorph.addLeft (1 : ℂ)).map_punctured_nhds_eq 0).le
    exact (isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <| H.isBigO_one ℂ
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhdsGT_le_nhdsNE 0

omit [NeZero N] in
/-
**DirichletCharacter.one_add_I_mul_ne_one_or** 是 Mathlib 中的一个引理，位于命名空间 `Dirichle
tCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma one_add_I_mul_ne_one_or {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    1 + I * y ≠ 1 ∨ χ ≠ 1 := by
  simpa only [ne_eq, add_eq_left, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
    using hy
/-
**DirichletCharacter.LFunction_isBigO_horizontal** 是 Mathlib 中的一个引理，位于命名空间 `Diri
chletCharacter`。
形式化陈述：LFunction_isBigO_horizontal {y : Real} (hy : y != 0 ∨ χ != 1) : (fun x : R
eal => LFunction χ (1 + x + I * y)) =O[𝓝[>] 0] fun _ => (1 : Complex)
参数：hy : y != 0 ∨ χ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DirichletCharacter.LFunction.congr_simp`：∀ {N : ℕ} [inst : NeZero N] (χ 
χ_1 : DirichletCharacter ℂ N),   χ = χ_1 → ∀ (s s_1 : ℂ), s = s_1 → DirichletCha
racter.LFunction χ s = Dirich…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `DirichletCharacter.differentiableAt_LFunction`：differentiableAt_LFunctio
n (χ : DirichletCharacter Complex N) (s : Complex) (hs : s != 1 ∨ χ != 1) : Diff
erentiableAt Complex (LFunction χ) …
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.Nonvanishing.0.DirichletCharacter.
one_add_I_mul_ne_one_or`：∀ {N : ℕ} (χ : DirichletCharacter ℂ N) {y : ℝ}, y ≠ 0 ∨
 χ ≠ 1 → 1 + Complex.I * ↑y ≠ 1 ∨ χ ≠ 1
· 使用定理 `Filter.Tendsto.isBigO_one`：∀ {α : Type u_1} (F : Type u_4) {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {f' : α → E'}   {l : Fil
ter α} [inst_2 …
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ContinuousAt.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : Topological
Space X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
lemma LFunction_isBigO_horizontal {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    (fun x : ℝ ↦ LFunction χ (1 + x + I * y)) =O[𝓝[>] 0] fun _ ↦ (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).continuousAt
  rw [← zero_add (1 + _)] at this
  exact this.comp (f := fun x : ℝ ↦ x + (1 + I * y)) (x := 0) (by fun_prop) |>.tendsto.isBigO_one ℂ
/-
**DirichletCharacter.LFunction_isBigO_horizontal_of_eq_zero** 是 Mathlib 中的一个引理，位
于命名空间 `DirichletCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma LFunction_isBigO_horizontal_of_eq_zero {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1)
    (h : LFunction χ (1 + I * y) = 0) :
    (fun x : ℝ ↦ LFunction χ (1 + x + I * y)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).hasDerivAt
  rw [← zero_add (1 + _)] at this
  simpa only [zero_add, h, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (this.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

-- intermediate statement, special case of the next theorem
/-
**DirichletCharacter.LFunction_ne_zero_of_not_quadratic_or_ne_one** 是 Mathlib 中的
一个引理，位于命名空间 `DirichletCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma LFunction_ne_zero_of_not_quadratic_or_ne_one {t : ℝ} (h : χ ^ 2 ≠ 1 ∨ t ≠ 0) :
    LFunction χ (1 + I * t) ≠ 0 := by
  intro Hz
  have hz₁ : t ≠ 0 ∨ χ ≠ 1 := by
    refine h.symm.imp_right (fun h H ↦ ?_)
    simp only [H, one_pow, ne_eq, not_true_eq_false] at h
  have hz₂ : 2 * t ≠ 0 ∨ χ ^ 2 ≠ 1 :=
    h.symm.imp_left <| mul_ne_zero two_ne_zero
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by lia), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  -- put together the various `IsBigO` statements and `norm_LFunction_product_ge_one`
  -- to derive a contradiction
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      fun x ↦ LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * t) ^ 4 *
                   LFunction (χ ^ 2) (1 + x + 2 * I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun _ hx ↦ (norm_one (α := ℝ)).symm ▸ (χ.norm_LFunction_product_ge_one hx t).le
  have H := (LFunctionTrivChar_isBigO_near_one_horizontal (N := N)).pow 3 |>.mul <|
    (χ.LFunction_isBigO_horizontal_of_eq_zero hz₁ Hz).pow 4 |>.mul <|
    LFunction_isBigO_horizontal _ hz₂
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  -- go via absolute value to translate into a statement over `ℝ`
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

/-- If `χ` is a Dirichlet character, then `L(χ, s)` does not vanish when `s.re = 1`
except when `χ` is trivial and `s = 1` (then `L(χ, s)` has a simple pole at `s = 1`). -/
/-
**DirichletCharacter.LFunction_ne_zero_of_re_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `D
irichletCharacter`。
形式化陈述：LFunction_ne_zero_of_re_eq_one {s : Complex} (hs : s.re = 1) (hχs : χ != 1
 ∨ s != 1) : LFunction χ s != 0
参数：hs : s.re = 1；hχs : χ != 1 ∨ s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.Nonvanishing.0.DirichletCharacter.
LFunction_apply_one_ne_zero_of_quadratic`：∀ {N : ℕ} [inst : NeZero N] {χ : Diric
hletCharacter ℂ N}, χ ^ 2 = 1 → χ ≠ 1 → DirichletCharacter.LFunction χ 1 ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.neg_resolve_right`：∀ {a b : Prop}, a ∨ ¬b → b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `add_ne_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b ≠ a ↔ b ≠ 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.Nonvanishing.0.DirichletCharacter.
LFunction_ne_zero_of_not_quadratic_or_ne_one`：∀ {N : ℕ} (χ : DirichletCharacter 
ℂ N) [inst : NeZero N] {t : ℝ},   χ ^ 2 ≠ 1 ∨ t ≠ 0 → DirichletCharacter.LFuncti
on χ (1 + Complex.I * ↑t) …

--- 原说明 ---
If `χ` is a Dirichlet character, then `L(χ, s)` does not vanish when `s.re = 1`
except when `χ` is trivial and `s = 1` (then `L(χ, s)` has a simple pole at `s =
 1`).
-/
theorem LFunction_ne_zero_of_re_eq_one {s : ℂ} (hs : s.re = 1) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s ≠ 0 := by
  by_cases h : χ ^ 2 = 1 ∧ s = 1
  · exact h.2 ▸ LFunction_apply_one_ne_zero_of_quadratic h.1 <| hχs.neg_resolve_right h.2
  · have hs' : s = 1 + I * s.im := by
      conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
    rw [not_and_or, ← ne_eq, ← ne_eq, hs', add_ne_left] at h
    replace h : χ ^ 2 ≠ 1 ∨ s.im ≠ 0 :=
      h.imp_right (fun H ↦ by exact_mod_cast right_ne_zero_of_mul H)
    exact hs'.symm ▸ χ.LFunction_ne_zero_of_not_quadratic_or_ne_one h

/-- If `χ` is a Dirichlet character, then `L(χ, s)` does not vanish for `s.re ≥ 1`
except when `χ` is trivial and `s = 1` (then `L(χ, s)` has a simple pole at `s = 1`). -/
/-
**DirichletCharacter.LFunction_ne_zero_of_one_le_re** 是 Mathlib 中的一个定理，位于命名空间 `D
irichletCharacter`。
形式化陈述：LFunction_ne_zero_of_one_le_re ⦃s : Complex⦄ (hχs : χ != 1 ∨ s != 1) (hs :
 1 <= s.re) : LFunction χ s != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`：LFunction_ne_zero_of_
re_eq_one {s : Complex} (hs : s.re = 1) (hχs : χ != 1 ∨ s != 1) : LFunction χ s 
!= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirichletCharacter.LSeries_ne_zero_of_one_lt_re`：LSeries_ne_zero_of_one_
lt_re {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
 : L ↗χ s != 0
· 使用引理 `DirichletCharacter.LFunction_eq_LSeries`：LFunction_eq_LSeries (χ : Diric
hletCharacter Complex N) {s : Complex} (hs : 1 < re s) : LFunction χ s = LSeries
 (χ ·) s

--- 原说明 ---
If `χ` is a Dirichlet character, then `L(χ, s)` does not vanish for `s.re ≥ 1`
except when `χ` is trivial and `s = 1` (then `L(χ, s)` has a simple pole at `s =
 1`).
-/
theorem LFunction_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    LFunction χ s ≠ 0 :=
  hs.eq_or_lt.casesOn (fun hs ↦ LFunction_ne_zero_of_re_eq_one χ hs.symm hχs)
    fun hs ↦ LFunction_eq_LSeries χ hs ▸ LSeries_ne_zero_of_one_lt_re χ hs

-- Interesting special case:
variable {χ} in
/-- The L-function of a nontrivial Dirichlet character does not vanish at `s = 1`. -/
/-
**DirichletCharacter.LFunction_apply_one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Diri
chletCharacter`。
形式化陈述：LFunction_apply_one_ne_zero (hχ : χ != 1) : LFunction χ 1 != 0
参数：hχ : χ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirichletCharacter.LFunction_ne_zero_of_one_le_re`：LFunction_ne_zero_of_
one_le_re ⦃s : Complex⦄ (hχs : χ != 1 ∨ s != 1) (hs : 1 <= s.re) : LFunction χ s
 != 0
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Complex.one_re`：one_re : (1 : Complex).re = 1

--- 原说明 ---
The L-function of a nontrivial Dirichlet character does not vanish at `s = 1`.
-/
theorem LFunction_apply_one_ne_zero (hχ : χ ≠ 1) : LFunction χ 1 ≠ 0 :=
  LFunction_ne_zero_of_one_le_re χ (.inl hχ) <| one_re ▸ le_rfl

/-- The Riemann Zeta Function does not vanish on the closed half-plane `re s ≥ 1`.
(Note that the value at `s = 1` is a junk value, which happens to be nonzero.) -/
/-
**DirichletCharacter._root_.riemannZeta_ne_zero_of_one_le_re** 是 Mathlib 中的一个引理，
位于命名空间 `DirichletCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Riemann Zeta Function does not vanish on the closed half-plane `re s ≥ 1`.
(Note that the value at `s = 1` is a junk value, which happens to be nonzero.)
-/
lemma _root_.riemannZeta_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs₀
  · exact riemannZeta_one_ne_zero
  · exact LFunction_modOne_eq (χ := 1) ▸ LFunction_ne_zero_of_one_le_re _ (.inr hs₀) hs

end nonvanishing

end DirichletCharacter

