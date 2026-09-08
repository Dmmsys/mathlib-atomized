/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Tactic.FieldSimp

/-!
# The Selberg Sieve

We set up the working assumptions of the Selberg sieve, define the notion of an upper bound sieve
and show that every upper bound sieve yields an upper bound on the size of the sifted set. We also
define the Λ² sieve and prove that Λ² sieves are upper bound sieves. We then diagonalise the main
term of the Λ² sieve.

We mostly follow the treatment outlined by Heath-Brown in the notes to an old graduate course. One
minor notational difference is that we write $\nu(n)$ in place of $\frac{\omega(n)}{n}$.

## Results
* `siftedSum_le_mainSum_errSum_of_UpperBoundSieve` - Every upper bound sieve gives an upper bound
  on the size of the sifted set in terms of `mainSum` and `errSum`
* `upperMoebius_of_lambda_sq` - Lambda squared weights produce upper bound sieves
* `lambdaSquared_mainSum_eq_diag_quad_form` - The main sum of a Λ² sieve has a nice diagonalisation

## References

* [Heath-Brown, *Lectures on sieves*][heathbrown2002lecturessieves]
* [Koukoulopoulos, *The Distribution of Prime Numbers*][MR3971232]

-/

@[expose] public section

noncomputable section

open scoped ArithmeticFunction.Moebius

open Finset Real Nat ArithmeticFunction

/-- We set up a sieve problem as follows. Take a finite set of natural numbers `A`, whose elements
are weighted by a sequence `a n`. Also take a finite set of primes `P`, represented by a squarefree
natural number. These are the primes that we will sift from our set `A`. Suppose we can approximate
`∑ n ∈ A with d ∣ n, a n = ν d * X + R d`, where `X` is an approximation to the total size of `A`
and `ν` is a multiplicative arithmetic function such that `0 < ν p < 1` for all primes `p ∣ P`.

Then a sieve-type theorem will give us an upper (or lower) bound on the size of the sifted sum
`∑ n ∈ support with n.Coprime P, a n`, obtained by removing any elements of `A` that are a
multiple of a prime in `P`. -/
/-
**BoundingSieve** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We set up a sieve problem as follows. Take a finite set of natural numbers `A`, 
whose elements
are weighted by a sequence `a n`. Also take a finite set of primes `P`, represen
ted by a squarefree
natural number. These are the primes that we will sift from our set `A`. Suppose
 we can approximate
`∑ n ∈ A with d ∣ n, a n = ν d * X + R d`, where `X` is an approximation to the 
total size of `A`
and `ν` is a multiplicative arithmetic function such that `0 < ν p < 1` for all 
primes `p ∣ P`.

Then a sieve-type theorem will give us an upper (or lower) bound on the size of 
the sifted sum
`∑ n ∈ support with n.Coprime P, a n`, obtained by removing any elements of `A` 
that are a
multiple of a prime in `P`.
-/
structure BoundingSieve where
  /-- The set of natural numbers that is to be sifted. The fundamental lemma yields an upper bound
  on the size of this set after the multiples of small primes have been removed. -/
  support : Finset ℕ
  /-- The finite set of prime numbers whose multiples are to be sifted from `support`. We work with
  their product because it lets us treat `nu` as a multiplicative arithmetic function. It also
  plays well with Moebius inversion. -/
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  /-- A sequence representing how much each element of `support` should be weighted. -/
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  /-- An approximation to `∑ i in support, weights i`, i.e. the size of the unsifted set. A bad
  approximation will yield a weak statement in the final theorem. -/
  totalMass : ℝ
  /-- `nu d` is an approximation to the proportion of elements of `support` that are a multiple of
  `d` -/
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → 0 < nu p
  nu_lt_one_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → nu p < 1

/-- The Selberg upper bound sieve in particular introduces a parameter called the `level` which
  gives the user control over the size of the error term. -/
/-
**SelbergSieve** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Selberg upper bound sieve in particular introduces a parameter called the `l
evel` which
  gives the user control over the size of the error term.
-/
structure SelbergSieve extends BoundingSieve where
  /-- The `level` of the sieve controls how many terms we include in the inclusion-exclusion type
  sum. A higher level will yield a tighter bound for the main term, but will also increase the
  size of the error term. -/
  level : ℝ
  one_le_level : 1 ≤ level

attribute [arith_mult] BoundingSieve.nu_mult

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `BoundingSieve.weights`. -/
@[positivity BoundingSieve.weights _ _]
meta def evalBoundingSieveWeights : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@BoundingSieve.weights $s $n) =>
    assertInstancesCommute
    pure (.nonnegative q(BoundingSieve.weights_nonneg $s $n))
  | _, _, _ => throwError "not BoundingSieve.weights"

end Mathlib.Meta.Positivity

namespace BoundingSieve
open SelbergSieve

/-
**BoundingSieve.one_le_y** 是 Mathlib 中的一个定理，位于命名空间 `BoundingSieve`。
形式化陈述：one_le_y {s : SelbergSieve} : 1 <= s.level
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SelbergSieve.one_le_level`：∀ (self : SelbergSieve), 1 ≤ self.level
-/
theorem one_le_y {s : SelbergSieve} : 1 ≤ s.level := s.one_le_level

variable {s : BoundingSieve}

/-! Lemmas about prodPrimes. -/

/-
**BoundingSieve.prodPrimes_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `BoundingSieve`。
形式化陈述：prodPrimes_ne_zero : s.prodPrimes != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `BoundingSieve.prodPrimes_squarefree`：∀ (self : BoundingSieve), Squarefre
e self.prodPrimes

--- 原说明 ---
Lemmas about prodPrimes.
-/
theorem prodPrimes_ne_zero : s.prodPrimes ≠ 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree
/-
**BoundingSieve.squarefree_of_dvd_prodPrimes** 是 Mathlib 中的一个定理，位于命名空间 `Bounding
Sieve`。
形式化陈述：squarefree_of_dvd_prodPrimes {d : Nat} (hd : d ∣ s.prodPrimes) : Squarefre
e d
参数：hd : d ∣ s.prodPrimes。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `BoundingSieve.prodPrimes_squarefree`：∀ (self : BoundingSieve), Squarefre
e self.prodPrimes
-/
theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ s.prodPrimes) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
/-
**BoundingSieve.squarefree_of_mem_divisors_prodPrimes** 是 Mathlib 中的一个定理，位于命名空间 
`BoundingSieve`。
形式化陈述：squarefree_of_mem_divisors_prodPrimes {d : Nat} (hd : d in divisors s.prod
Primes) : Squarefree d
参数：hd : d in divisors s.prodPrimes。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoundingSieve.prodPrimes_squarefree`：∀ (self : BoundingSieve), Squarefre
e self.prodPrimes
-/
theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors s.prodPrimes) :
    Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

/-! Lemmas about $\nu$. -/

/-
**BoundingSieve.prod_primeFactors_nu** 是 Mathlib 中的一个定理，位于命名空间 `BoundingSieve`。
形式化陈述：prod_primeFactors_nu {d : Nat} (hd : d ∣ s.prodPrimes) : ∏ p in d.primeFac
tors, s.nu p = s.nu d
参数：hd : d ∣ s.prodPrimes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors`：map
_prod_of_subset_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R} (
h_mult : ArithmeticFunction.IsMultiplicative f) (l : Nat)…
· 使用定理 `BoundingSieve.nu_mult`：∀ (self : BoundingSieve), self.nu.IsMultiplicativ
e
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用引理 `Nat.prod_primeFactors_of_squarefree`：prod_primeFactors_of_squarefree (hn
 : Squarefree n) : ∏ p in n.primeFactors, p = n
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `BoundingSieve.prodPrimes_squarefree`：∀ (self : BoundingSieve), Squarefre
e self.prodPrimes

--- 原说明 ---
Lemmas about $\nu$.
-/
theorem prod_primeFactors_nu {d : ℕ} (hd : d ∣ s.prodPrimes) :
    ∏ p ∈ d.primeFactors, s.nu p = s.nu d := by
  rw [← s.nu_mult.map_prod_of_subset_primeFactors _ _ subset_rfl,
    Nat.prod_primeFactors_of_squarefree <| Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree]
/-
**BoundingSieve.nu_pos_of_dvd_prodPrimes** 是 Mathlib 中的一个定理，位于命名空间 `BoundingSiev
e`。
形式化陈述：nu_pos_of_dvd_prodPrimes {d : Nat} (hd : d ∣ s.prodPrimes) : 0 < s.nu d
参数：hd : d ∣ s.prodPrimes。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `Nat.dvd_of_mem_primeFactors`：dvd_of_mem_primeFactors (hp : p in n.primeF
actors) : p ∣ n
· 使用定理 `BoundingSieve.nu_pos_of_prime`：∀ (self : BoundingSieve) (p : ℕ), Nat.Pri
me p → p ∣ self.prodPrimes → 0 < self.nu p
· 使用定理 `BoundingSieve.prod_primeFactors_nu`：prod_primeFactors_nu {d : Nat} (hd :
 d ∣ s.prodPrimes) : ∏ p in d.primeFactors, s.nu p = s.nu d
-/
theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ s.prodPrimes) : 0 < s.nu d := by
  calc
    0 < ∏ p ∈ d.primeFactors, s.nu p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ s.prodPrimes := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = s.nu d := prod_primeFactors_nu hd
/-
**BoundingSieve.nu_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `BoundingSieve`。
形式化陈述：nu_ne_zero {d : Nat} (hd : d ∣ s.prodPrimes) : s.nu d != 0
参数：hd : d ∣ s.prodPrimes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `BoundingSieve.nu_pos_of_dvd_prodPrimes`：nu_pos_of_dvd_prodPrimes {d : Na
t} (hd : d ∣ s.prodPrimes) : 0 < s.nu d
-/
theorem nu_ne_zero {d : ℕ} (hd : d ∣ s.prodPrimes) : s.nu d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes hd
/-
**BoundingSieve.nu_lt_one_of_dvd_prodPrimes** 是 Mathlib 中的一个定理，位于命名空间 `BoundingS
ieve`。
形式化陈述：nu_lt_one_of_dvd_prodPrimes {d : Nat} (hdP : d ∣ s.prodPrimes) (hd_ne_one 
: d != 1) : s.nu d < 1
参数：hdP : d ∣ s.prodPrimes；hd_ne_one : d != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `BoundingSieve.prodPrimes_squarefree`：∀ (self : BoundingSieve), Squarefre
e self.prodPrimes
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoundingSieve.prod_primeFactors_nu`：prod_primeFactors_nu {d : Nat} (hd :
 d ∣ s.prodPrimes) : ∏ p in d.primeFactors, s.nu p = s.nu d
· 使用引理 `Finset.prod_lt_prod_of_nonempty`：prod_lt_prod_of_nonempty (hf : forall i
 in s, 0 < f i) (hfg : forall i in s, f i < g i) (h_ne : s.Nonempty) : ∏ i in s,
 f i < ∏ i in s, g i
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `BoundingSieve.nu_pos_of_prime`：∀ (self : BoundingSieve) (p : ℕ), Nat.Pri
me p → p ∣ self.prodPrimes → 0 < self.nu p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoundingSieve.nu_lt_one_of_prime`：∀ (self : BoundingSieve) (p : ℕ), Nat.
Prime p → p ∣ self.prodPrimes → self.nu p < 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.mem_primeFactors_of_ne_zero`：mem_primeFactors_of_ne_zero (hn : n != 
0) : p in n.primeFactors ↔ p.Prime ∧ p ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nu_lt_one_of_dvd_prodPrimes {d : ℕ} (hdP : d ∣ s.prodPrimes) (hd_ne_one : d ≠ 1) :
    s.nu d < 1 := by
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  have := hd_sq.ne_zero
  calc
    s.nu d = ∏ p ∈ d.primeFactors, s.nu p := (prod_primeFactors_nu hdP).symm
    _ < ∏ p ∈ d.primeFactors, 1 := by
      apply prod_lt_prod_of_nonempty
      · intro p hp
        simp only [mem_primeFactors] at hp
        apply s.nu_pos_of_prime p hp.1 (hp.2.1.trans hdP)
      · intro p hpd; rw [mem_primeFactors_of_ne_zero hd_sq.ne_zero] at hpd
        apply s.nu_lt_one_of_prime p hpd.left (hpd.2.trans hdP)
      · simp only [nonempty_primeFactors, show 1 < d by lia]
    _ = 1 := by
      simp

/-- The weight of all the elements that are a multiple of `d`. -/
@[simp]
/-
**BoundingSieve.multSum** 是 Mathlib 中的一个定义，位于命名空间 `BoundingSieve`。
形式化陈述：multSum (d : Nat) : Real
参数：d : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight of all the elements that are a multiple of `d`.
-/
def multSum (d : ℕ) : ℝ := ∑ n ∈ s.support, if d ∣ n then s.weights n else 0


/-- The remainder term in the approximation A_d = ν (d) X + R_d. This is the degree to which `nu`
  fails to approximate the proportion of the weight that is a multiple of `d`. -/
@[simp]
/-
**BoundingSieve.rem** 是 Mathlib 中的一个定义，位于命名空间 `BoundingSieve`。
形式化陈述：rem (d : Nat) : Real
参数：d : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The remainder term in the approximation A_d = ν (d) X + R_d. This is the degree 
to which `nu`
  fails to approximate the proportion of the weight that is a multiple of `d`.
-/
def rem (d : ℕ) : ℝ := s.multSum d - s.nu d * s.totalMass

/-- The weight of all the elements that are not a multiple of any of our finite set of primes. -/
/-
**BoundingSieve.siftedSum** 是 Mathlib 中的一个定义，位于命名空间 `BoundingSieve`。
形式化陈述：siftedSum : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight of all the elements that are not a multiple of any of our finite set 
of primes.
-/
def siftedSum : ℝ := ∑ d ∈ s.support, if Coprime s.prodPrimes d then s.weights d else 0

/-- `X * mainSum μ⁺` is the main term in the upper bound on `sifted_sum`. -/
/-
**BoundingSieve.mainSum** 是 Mathlib 中的一个定义，位于命名空间 `BoundingSieve`。
形式化陈述：mainSum (muPlus : Nat -> Real) : Real
参数：muPlus : Nat -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X * mainSum μ⁺` is the main term in the upper bound on `sifted_sum`.
-/
def mainSum (muPlus : ℕ → ℝ) : ℝ := ∑ d ∈ divisors s.prodPrimes, muPlus d * s.nu d

/-- `errSum μ⁺` is the error term in the upper bound on `sifted_sum`. -/
/-
**BoundingSieve.errSum** 是 Mathlib 中的一个定义，位于命名空间 `BoundingSieve`。
形式化陈述：errSum (muPlus : Nat -> Real) : Real
参数：muPlus : Nat -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`errSum μ⁺` is the error term in the upper bound on `sifted_sum`.
-/
def errSum (muPlus : ℕ → ℝ) : ℝ := ∑ d ∈ divisors s.prodPrimes, |muPlus d| * |s.rem d|
/-
**BoundingSieve.multSum_eq_main_err** 是 Mathlib 中的一个定理，位于命名空间 `BoundingSieve`。
形式化陈述：multSum_eq_main_err (d : Nat) : s.multSum d = s.nu d * s.totalMass + s.rem
 d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundingSieve.rem.eq_1`：∀ {s : BoundingSieve} (d : ℕ), BoundingSieve.rem
 d = BoundingSieve.multSum d - s.nu d * s.totalMass
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 33 条，此处仅展示前 30 条）
-/
theorem multSum_eq_main_err (d : ℕ) : s.multSum d = s.nu d * s.totalMass + s.rem d := by
  rw [rem]
  ring
/-
**BoundingSieve.siftedSum_eq_sum_support_mul_ite** 是 Mathlib 中的一个定理，位于命名空间 `Boun
dingSieve`。
形式化陈述：siftedSum_eq_sum_support_mul_ite : s.siftedSum = ∑ d in s.support, s.weigh
ts d * if Nat.gcd s.prodPrimes d = 1 then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundingSieve.siftedSum.eq_1`：∀ {s : BoundingSieve}, BoundingSieve.sifte
dSum = ∑ d ∈ s.support, if s.prodPrimes.Coprime d then s.weights d else 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem siftedSum_eq_sum_support_mul_ite :
    s.siftedSum = ∑ d ∈ s.support, s.weights d * if Nat.gcd s.prodPrimes d = 1 then 1 else 0 := by
  rw [siftedSum]
  simp_rw [mul_ite, mul_one, mul_zero]

omit s in
/-- A sequence of coefficients $\mu^{+}$ is upper Moebius if $\mu * \zeta ≤ \mu^{+} * \zeta$. These
  coefficients then yield an upper bound on the sifted sum. -/
/-
**BoundingSieve.IsUpperMoebius** 是 Mathlib 中的一个定义，位于命名空间 `BoundingSieve`。
形式化陈述：IsUpperMoebius (muPlus : Nat -> Real) : Prop
参数：muPlus : Nat -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of coefficients $\mu^{+}$ is upper Moebius if $\mu * \zeta ≤ \mu^{+} 
* \zeta$. These
  coefficients then yield an upper bound on the sifted sum.
-/
def IsUpperMoebius (muPlus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d
/-
**BoundingSieve.siftedSum_le_sum_of_upperMoebius** 是 Mathlib 中的一个定理，位于命名空间 `Boun
dingSieve`。
形式化陈述：siftedSum_le_sum_of_upperMoebius (muPlus : Nat -> Real) (h : IsUpperMoebiu
s muPlus) : s.siftedSum <= ∑ d in divisors s.prodPrimes, muPlus d * s.multSum d
参数：muPlus : Nat -> Real；h : IsUpperMoebius muPlus。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundingSieve.siftedSum_eq_sum_support_mul_ite`：siftedSum_eq_sum_support
_mul_ite : s.siftedSum = ∑ d in s.support, s.weights d * if Nat.gcd s.prodPrimes
 d = 1 then 1 else 0
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `BoundingSieve.weights_nonneg`：∀ (self : BoundingSieve) (n : ℕ), 0 ≤ self
.weights n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.divisors_filter_dvd_of_dvd`：divisors_filter_dvd_of_dvd {n m : Nat} (
hn : n != 0) (hm : m ∣ n) : {d in n.divisors | d ∣ m} = m.divisors
· 使用定理 `BoundingSieve.prodPrimes_ne_zero`：prodPrimes_ne_zero : s.prodPrimes != 0
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.dvd_gcd_iff`：∀ {k : ℕ} {m n : ℕ}, k ∣ m.gcd n ↔ k ∣ m ∧ k ∣ n
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem siftedSum_le_sum_of_upperMoebius (muPlus : ℕ → ℝ) (h : IsUpperMoebius muPlus) :
    s.siftedSum ≤ ∑ d ∈ divisors s.prodPrimes, muPlus d * s.multSum d := by
  have hμ : ∀ n, (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d := h
  calc siftedSum ≤
    ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muPlus d := ?caseA
    _ = ∑ n ∈ s.support, ∑ d ∈ divisors s.prodPrimes,
        if d ∣ n then s.weights n * muPlus d else 0 := ?caseB
    _ = ∑ d ∈ divisors s.prodPrimes, muPlus d * multSum d := ?caseC
  case caseA =>
    rw [siftedSum_eq_sum_support_mul_ite]
    gcongr with n
    exact hμ (Nat.gcd s.prodPrimes n)
  case caseB =>
    simp_rw [mul_sum, ← sum_filter]
    congr with n
    congr
    · rw [← divisors_filter_dvd_of_dvd prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
      ext x; simp +contextual [dvd_gcd_iff]
  case caseC =>
    rw [sum_comm]
    simp_rw [multSum, ← sum_filter, mul_sum, mul_comm]
/-
**BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius** 是 Mathlib 中的一个定理，位
于命名空间 `BoundingSieve`。
形式化陈述：siftedSum_le_mainSum_errSum_of_upperMoebius (muPlus : Nat -> Real) (h : Is
UpperMoebius muPlus) : s.siftedSum <= s.totalMass * s.mainSum muPlus + s.errSum 
muPlus
参数：muPlus : Nat -> Real；h : IsUpperMoebius muPlus。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundingSieve.siftedSum_le_sum_of_upperMoebius`：siftedSum_le_sum_of_uppe
rMoebius (muPlus : Nat -> Real) (h : IsUpperMoebius muPlus) : s.siftedSum <= ∑ d
 in divisors s.prodPrimes, muPlus d …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundingSieve.mainSum.eq_1`：∀ {s : BoundingSieve} (muPlus : ℕ → ℝ), Boun
dingSieve.mainSum muPlus = ∑ d ∈ s.prodPrimes.divisors, muPlus d * s.nu d
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `BoundingSieve.rem.eq_1`：∀ {s : BoundingSieve} (d : ℕ), BoundingSieve.rem
 d = BoundingSieve.multSum d - s.nu d * s.totalMass
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 47 条，此处仅展示前 30 条）
-/
theorem siftedSum_le_mainSum_errSum_of_upperMoebius (muPlus : ℕ → ℝ) (h : IsUpperMoebius muPlus) :
    s.siftedSum ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus := calc
  s.siftedSum ≤ ∑ d ∈ divisors s.prodPrimes, muPlus d * multSum d :=
    siftedSum_le_sum_of_upperMoebius _ h
  _ = s.totalMass * mainSum muPlus + ∑ d ∈ divisors s.prodPrimes, muPlus d * s.rem d := by
    rw [mainSum, mul_sum, ← sum_add_distrib]
    congr with d
    rw [rem]
    ring
  _ ≤ s.totalMass * mainSum muPlus + errSum muPlus := by
    rw [errSum]
    gcongr _ + ∑ d ∈ _, ?_ with d
    rw [← abs_mul]
    exact le_abs_self (muPlus d * s.rem d)

section LambdaSquared

/-- We consider a special class of upper bound sieves called the Λ² sieve. This class is
  parameterised by a sequence of real numbers. We will later choose a set of weights that minimises
  the main term, under a constraint that lets us control the error term. -/
/-
**BoundingSieve.lambdaSquared** 是 Mathlib 中的一个定义，位于命名空间 `BoundingSieve`。
形式化陈述：lambdaSquared (weights : Nat -> Real) : Nat -> Real
参数：weights : Nat -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We consider a special class of upper bound sieves called the Λ² sieve. This clas
s is
  parameterised by a sequence of real numbers. We will later choose a set of wei
ghts that minimises
  the main term, under a constraint that lets us control the error term.
-/
def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0
/-
**BoundingSieve.sum_divisors_lambda_sq_larger_sum** 是 Mathlib 中的一个定理，位于命名空间 `Bou
ndingSieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sum_divisors_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
    (∑ d ∈ n.divisors, ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
     if d = Nat.lcm d1 d2 then f d1 d2 d else 0) := by
  congr! 1 with d hd
  rw [mem_divisors] at hd
  suffices ∀ d1 d2, (d1 ∣ d ∧ d2 ∣ d ∧ d = d1.lcm d2) = (d = d1.lcm d2) by
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ite_sum_zero, ← ite_and, this]
  simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
/-
**BoundingSieve.upperMoebius_lambdaSquared** 是 Mathlib 中的一个定理，位于命名空间 `BoundingSi
eve`。
形式化陈述：upperMoebius_lambdaSquared (weights : Nat -> Real) (hw : weights 1 = 1) : 
IsUpperMoebius lambdaSquared weights
参数：weights : Nat -> Real；hw : weights 1 = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisors_one`：divisors_one : divisors 1 = {1}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.lcm_one_right`：∀ (m : ℕ), m.lcm 1 = m
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `_private.Mathlib.NumberTheory.SelbergSieve.0.BoundingSieve.sum_divisors_
lambda_sq_larger_sum`：∀ (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ),   (∑ d ∈ n.divisors, ∑ d1 ∈
 d.divisors, ∑ d2 ∈ d.divisors, if d = d1.lcm d2 then f d1 d2 d else 0) =     ∑ 
d …
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_ite_eq_of_mem'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCo
mmMonoid M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   a ∈ s
 → (∑ x ∈ s, if…
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
（共 35 条，此处仅展示前 30 条）
-/
theorem upperMoebius_lambdaSquared (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius <| lambdaSquared weights := by
  dsimp only [IsUpperMoebius, lambdaSquared]
  intro n
  split_ifs
  · simp_all
  grw [sq_nonneg (∑ d ∈ n.divisors, weights d), sum_divisors_lambda_sq_larger_sum _ n, sum_comm]
  apply le_of_eq
  simp_rw [sq, mul_sum, sum_mul]
  congr! 1 with d1 hd1
  rw [sum_comm]
  congr! 1 with d2 hd2
  rw [sum_ite_eq_of_mem', mul_comm]
  -- Deal with the side goal from `sum_ite_eq_of_mem'`
  rw [mem_divisors, Nat.lcm_dvd_iff]
  exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩

end LambdaSquared

section SelbergTerms

variable {s : BoundingSieve}

/-- These are the terms that appear in the sum `S` in the main term of the fundamental theorem.

$$S = \sum_{l \mid P, l \le \sqrt{y}} g(l)$$ -/
/-
**BoundingSieve.selbergTerms** 是 Mathlib 中的一个定义，位于命名空间 `BoundingSieve`。
形式化陈述：selbergTerms : ArithmeticFunction Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These are the terms that appear in the sum `S` in the main term of the fundament
al theorem.

$$S = \sum_{l \mid P, l \le \sqrt{y}} g(l)$$
-/
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p ↦  (1 - s.nu p)⁻¹)
/-
**BoundingSieve.selbergTerms_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundingSieve`。
形式化陈述：selbergTerms_apply (d : Nat) : s.selbergTerms d = s.nu d * ∏ p in d.primeF
actors, (1 - s.nu p)⁻¹
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `Finset.prod_inv_distrib`：prod_inv_distrib (f : ι -> G) : (∏ x in s, (f x
)⁻¹) = (∏ x in s, f x)⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ArithmeticFunction.pmul_apply`：pmul_apply [MulZeroClass R] {f g : Arithm
eticFunction R} {x : Nat} : f.pmul g x = f x * g x
· 使用定理 `ArithmeticFunction.prodPrimeFactors_apply`：prodPrimeFactors_apply [CommM
onoidWithZero R] {f : Nat -> R} {n : Nat} (hn : n != 0) : ∏ᵖ p ∣ n, f p = ∏ p in
 n.primeFactors, f p
-/
theorem selbergTerms_apply (d : ℕ) :
    s.selbergTerms d = s.nu d * ∏ p ∈ d.primeFactors, (1 - s.nu p)⁻¹ := by
  unfold selbergTerms
  by_cases h : d = 0
  · simp [h]
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]

/-! Now follow some important identities involving `selbergTerms` -/

/-
**BoundingSieve.selbergTerms_pos** 是 Mathlib 中的一个定理，位于命名空间 `BoundingSieve`。
形式化陈述：selbergTerms_pos {l : Nat} (hl : l ∣ s.prodPrimes) : 0 < s.selbergTerms l
参数：hl : l ∣ s.prodPrimes。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundingSieve.selbergTerms_apply`：selbergTerms_apply (d : Nat) : s.selbe
rgTerms d = s.nu d * ∏ p in d.primeFactors, (1 - s.nu p)⁻¹
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `BoundingSieve.nu_pos_of_dvd_prodPrimes`：nu_pos_of_dvd_prodPrimes {d : Na
t} (hd : d ∣ s.prodPrimes) : 0 < s.nu d
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `Nat.dvd_of_mem_primeFactors`：dvd_of_mem_primeFactors (hp : p in n.primeF
actors) : p ∣ n
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Now follow some important identities involving `selbergTerms`
-/
theorem selbergTerms_pos {l : ℕ} (hl : l ∣ s.prodPrimes) : 0 < s.selbergTerms l := by
  rw [selbergTerms_apply]
  refine mul_pos (nu_pos_of_dvd_prodPrimes hl) <| prod_pos fun p hp ↦ ?_
  rw [inv_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]
/-
**BoundingSieve.selbergTerms_isMultiplicative** 是 Mathlib 中的一个定理，位于命名空间 `Boundin
gSieve`。
形式化陈述：selbergTerms_isMultiplicative : ArithmeticFunction.IsMultiplicative s.selb
ergTerms
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.IsMultiplicative.pmul`：pmul [CommSemiring R] {f g : A
rithmeticFunction R} (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : IsMul
tiplicative (f.pmul g)
· 使用定理 `BoundingSieve.nu_mult`：∀ (self : BoundingSieve), self.nu.IsMultiplicativ
e
· 使用定理 `ArithmeticFunction.IsMultiplicative.prodPrimeFactors`：prodPrimeFactors [
CommMonoidWithZero R] (f : Nat -> R) : IsMultiplicative (prodPrimeFactors f)
-/
theorem selbergTerms_isMultiplicative : ArithmeticFunction.IsMultiplicative s.selbergTerms := by
  unfold selbergTerms
  arith_mult
/-
**BoundingSieve.inv_selbergTerms_eq_sum_divisors_moebius_nu** 是 Mathlib 中的一个定理，位
于命名空间 `BoundingSieve`。
形式化陈述：inv_selbergTerms_eq_sum_divisors_moebius_nu {l : Nat} (hl : Squarefree l) 
(hnu_nonzero : s.nu l != 0) : (s.selbergTerms l)⁻¹ = ∑ ⟨d, e⟩ in l.divisorsAntid
iagonal, (μ d) * (s.nu e)⁻¹
参数：hl : Squarefree l；hnu_nonzero : s.nu l != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoundingSieve.selbergTerms_apply`：selbergTerms_apply (d : Nat) : s.selbe
rgTerms d = s.nu d * ∏ p in d.primeFactors, (1 - s.nu p)⁻¹
· 使用定理 `Finset.prod_inv_distrib`：prod_inv_distrib (f : ι -> G) : (∏ x in s, (f x
)⁻¹) = (∏ x in s, f x)⁻¹
· 使用定理 `ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefr
ee`：∀ {R : Type u_1} [inst : CommRing R] (f : ArithmeticFunction R),   f.IsMulti
plicative →     ∀ {n : ℕ}, Squarefree n → ∏ p ∈ n.primeFactors, …
· 使用定理 `BoundingSieve.nu_mult`：∀ (self : BoundingSieve), self.nu.IsMultiplicativ
e
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sum_divisorsAntidiagonal`：∀ {M : Type u_1} [inst : AddCommMonoid M] 
(f : ℕ → ℕ → M) {n : ℕ},   ∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.div
isors, f i (n / i)
· 使用定理 `Nat.squarefree_mul_iff`：squarefree_mul_iff {m n : Nat} : Squarefree (m *
 n) ↔ m.Coprime n ∧ Squarefree m ∧ Squarefree n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime`：map_mul_of_copri
me {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : Nat} (h : m.gcd n
 = 1) : f (m * n) = f m * f n
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 52 条，此处仅展示前 30 条）
-/
theorem inv_selbergTerms_eq_sum_divisors_moebius_nu {l : ℕ} (hl : Squarefree l)
    (hnu_nonzero : s.nu l ≠ 0) :
    (s.selbergTerms l)⁻¹ = ∑ ⟨d, e⟩ ∈ l.divisorsAntidiagonal, (μ d) * (s.nu e)⁻¹ := by
  simp only [selbergTerms_apply, mul_inv, inv_inv,
    Finset.prod_inv_distrib, s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ hl, mul_sum]
  rw [← Nat.sum_divisorsAntidiagonal fun i _ : ℕ ↦ (s.nu l)⁻¹ * (↑(μ i) * s.nu i)]
  congr! 1 with ⟨d, e⟩ hd
  obtain ⟨rfl, -⟩ : d * e = l ∧ _ := by simpa using hd
  obtain ⟨hde, -⟩ : d.Coprime e ∧ _ := by simpa only [squarefree_mul_iff] using hl
  obtain ⟨hd0, he0⟩ : ¬s.nu d = 0 ∧ ¬s.nu e = 0 := by simp_all [s.nu_mult.map_mul_of_coprime hde]
  simp [field, s.nu_mult.map_mul_of_coprime hde, mul_assoc]
/-
**BoundingSieve.nu_inv_eq_sum_divisors_inv_selbergTerms** 是 Mathlib 中的一个定理，位于命名空
间 `BoundingSieve`。
形式化陈述：nu_inv_eq_sum_divisors_inv_selbergTerms {d : Nat} (hdP : d ∣ s.prodPrimes)
 : (s.nu d)⁻¹ = ∑ l in divisors s.prodPrimes, if l ∣ d then (s.selbergTerms l)⁻¹
 else 0
参数：hdP : d ∣ s.prodPrimes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用引理 `Nat.divisors_filter_dvd_of_dvd`：divisors_filter_dvd_of_dvd {n m : Nat} (
hn : n != 0) (hm : m ∣ n) : {d in n.divisors | d ∣ m} = m.divisors
· 使用定理 `BoundingSieve.prodPrimes_ne_zero`：prodPrimes_ne_zero : s.prodPrimes != 0
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on`：sum_eq_iff_sum_mul_
moebius_eq_on [NonAssocRing R] {f g : Nat -> R} (s : Set Nat) (hs : forall m n, 
m ∣ n -> n in s -> m in s) : (forall n > …
· 使用定理 `Nat.dvd_trans`：∀ {a b c : ℕ}, a ∣ b → b ∣ c → a ∣ c
· 使用定理 `BoundingSieve.inv_selbergTerms_eq_sum_divisors_moebius_nu`：inv_selbergTe
rms_eq_sum_divisors_moebius_nu {l : Nat} (hl : Squarefree l) (hnu_nonzero : s.nu
 l != 0) : (s.selbergTerms l)⁻¹ = ∑ ⟨d, e⟩ in l…
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `BoundingSieve.prodPrimes_squarefree`：∀ (self : BoundingSieve), Squarefre
e self.prodPrimes
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `BoundingSieve.nu_pos_of_dvd_prodPrimes`：nu_pos_of_dvd_prodPrimes {d : Na
t} (hd : d ∣ s.prodPrimes) : 0 < s.nu d
-/
theorem nu_inv_eq_sum_divisors_inv_selbergTerms {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    (s.nu d)⁻¹ = ∑ l ∈ divisors s.prodPrimes, if l ∣ d then (s.selbergTerms l)⁻¹ else 0 := by
  rw [eq_comm, ← sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ ↦ Nat.dvd_trans)).mpr
  intro l _ hlP
  exact inv_selbergTerms_eq_sum_divisors_moebius_nu
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP) |>.symm
/-
**BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv** 是 Mathlib
 中的一个定理，位于命名空间 `BoundingSieve`。
形式化陈述：sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv {d : Nat} (hd : d ∣ s
.prodPrimes) : (∑ l in divisors s.prodPrimes, if l ∣ d then s.selbergTerms l els
e 0) = s.selbergTerms d * (s.nu d)⁻¹
参数：hd : d ∣ s.prodPrimes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Nat.divisors_filter_dvd_of_dvd`：divisors_filter_dvd_of_dvd {n m : Nat} (
hn : n != 0) (hm : m ∣ n) : {d in n.divisors | d ∣ m} = m.divisors
· 使用定理 `BoundingSieve.prodPrimes_ne_zero`：prodPrimes_ne_zero : s.prodPrimes != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.sum_div_divisors`：∀ {α : Type u_1} [inst : AddCommMonoid α] (n : ℕ) 
(f : ℕ → α), ∑ d ∈ n.divisors, f (n / d) = n.divisors.sum f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_div_of_coprime`：map_div_of_copri
me [GroupWithZero R] {f : ArithmeticFunction R} (hf : IsMultiplicative f) {l d :
 Nat} (hdl : d ∣ l) (hl : (l / d).Coprime d)…
· 使用定理 `BoundingSieve.selbergTerms_isMultiplicative`：selbergTerms_isMultiplicati
ve : ArithmeticFunction.IsMultiplicative s.selbergTerms
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.coprime_of_squarefree_mul`：coprime_of_squarefree_mul {m n : Nat} (h 
: Squarefree (m * n)) : m.Coprime n
· 使用定理 `BoundingSieve.squarefree_of_dvd_prodPrimes`：squarefree_of_dvd_prodPrimes
 {d : Nat} (hd : d ∣ s.prodPrimes) : Squarefree d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `BoundingSieve.selbergTerms_pos`：selbergTerms_pos {l : Nat} (hl : l ∣ s.p
rodPrimes) : 0 < s.selbergTerms l
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
（共 44 条，此处仅展示前 30 条）
-/
theorem sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then s.selbergTerms l else 0) =
      s.selbergTerms d * (s.nu d)⁻¹ := by
  calc
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then s.selbergTerms l else 0) =
        ∑ l ∈ divisors s.prodPrimes, if l ∣ d then s.selbergTerms (d / l) else 0 := by
      simp_rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hd,
        sum_div_divisors d s.selbergTerms]
    _ = s.selbergTerms d *
          ∑ l ∈ divisors s.prodPrimes, if l ∣ d then (s.selbergTerms l)⁻¹ else 0 := by
      simp_rw [← sum_filter, mul_sum]
      congr! 1 with l hl
      simp only [mem_filter, mem_divisors, ne_eq] at hl
      rw [selbergTerms_isMultiplicative.map_div_of_coprime hl.2]
      · ring
      · apply coprime_of_squarefree_mul <|
          (Nat.div_mul_cancel hl.2).symm ▸ (squarefree_of_dvd_prodPrimes hd)
      · exact (selbergTerms_pos hl.1.1).ne'
    _ = s.selbergTerms d * (s.nu d)⁻¹ := by rw [← nu_inv_eq_sum_divisors_inv_selbergTerms hd]

end SelbergTerms

section QuadForm

/-- The main sum we get from Λ² coefficients is a quadratic form. Used to prove the Selberg sieve
  identity by choosing weights that maximize this sum. -/
/-
**BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul** 是 Mathlib 中的一个定理，位于命名空间 `
BoundingSieve`。
形式化陈述：mainSum_lambdaSquared_eq_sum_sum_mul (w : Nat -> Real) : s.mainSum (lambda
Squared w) = ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes, s.nu 
d1 * w d1 * s.nu d2 * w d2 * (s.nu (d1.gcd d2))⁻¹
参数：w : Nat -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.NumberTheory.SelbergSieve.0.BoundingSieve.sum_divisors_
lambda_sq_larger_sum`：∀ (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ),   (∑ d ∈ n.divisors, ∑ d1 ∈
 d.divisors, ∑ d2 ∈ d.divisors, if d = d1.lcm d2 then f d1 d2 d else 0) =     ∑ 
d …
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lcm_dvd_iff`：∀ {m n k : ℕ}, m.lcm n ∣ k ↔ m ∣ k ∧ n ∣ k
· 使用定理 `Nat.dvd_of_mem_divisors`：dvd_of_mem_divisors {m : Nat} (h : n in divisor
s m) : n ∣ m
· 使用定理 `Finset.sum_ite_eq_of_mem'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCo
mmMonoid M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   a ∈ s
 → (∑ x ∈ s, if…
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `BoundingSieve.prodPrimes_ne_zero`：prodPrimes_ne_zero : s.prodPrimes != 0
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_lcm`：map_lcm [CommGroupWithZero 
R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {x y : Nat} (hf_gcd : f 
(x.gcd y) != 0) : f (x.lcm y) = f…
· 使用定理 `BoundingSieve.nu_mult`：∀ (self : BoundingSieve), self.nu.IsMultiplicativ
e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `BoundingSieve.nu_pos_of_dvd_prodPrimes`：nu_pos_of_dvd_prodPrimes {d : Na
t} (hd : d ∣ s.prodPrimes) : 0 < s.nu d
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
The main sum we get from Λ² coefficients is a quadratic form. Used to prove the 
Selberg sieve
  identity by choosing weights that maximize this sum.
-/
theorem mainSum_lambdaSquared_eq_sum_sum_mul (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
        s.nu d1 * w d1 * s.nu d2 * w d2 * (s.nu (d1.gcd d2))⁻¹ := by
  calc mainSum (lambdaSquared w)
      = ∑ d ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := ?caseA
    _ = ∑ d ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := sum_divisors_lambda_sq_larger_sum _ _
    _ = ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
          s.nu d1 * w d1 * s.nu d2 * w d2 * (s.nu (d1.gcd d2))⁻¹ := ?caseB
  case caseA =>
    simp [mainSum, lambdaSquared, sum_mul]
  case caseB =>
    rw [sum_comm, sum_congr rfl]; intro d1 hd1
    rw [sum_comm, sum_congr rfl]; intro d2 hd2
    have h : d1.lcm d2 ∣ s.prodPrimes :=
      Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
    rw [sum_ite_eq_of_mem' (divisors s.prodPrimes) (d1.lcm d2) _
      (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩), s.nu_mult.map_lcm]
    · ring
    refine (nu_pos_of_dvd_prodPrimes ?_).ne'
    exact (Nat.gcd_dvd_left d1 d2).trans (dvd_of_mem_divisors hd1)

/-- The main sum we get from Λ² coefficients can be written as a diagonalized quadratic form with
  eigenvalues given by `1/selbergTerms` -/
/-
**BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq** 是 Mathlib 中的一个定理，位于命名空
间 `BoundingSieve`。
形式化陈述：mainSum_lambdaSquared_eq_sum_mul_sum_sq (w : Nat -> Real) : s.mainSum (lam
bdaSquared w) = ∑ l in divisors s.prodPrimes, (s.selbergTerms l)⁻¹ * (∑ d in div
isors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2
参数：w : Nat -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul`：mainSum_lambdaSquare
d_eq_sum_sum_mul (w : Nat -> Real) : s.mainSum (lambdaSquared w) = ∑ d1 in divis
ors s.prodPrimes, ∑ d2 in divisors s.pro…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Nat.dvd_of_mem_divisors`：dvd_of_mem_divisors {m : Nat} (h : n in divisor
s m) : n ∣ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoundingSieve.nu_inv_eq_sum_divisors_inv_selbergTerms`：nu_inv_eq_sum_div
isors_inv_selbergTerms {d : Nat} (hdP : d ∣ s.prodPrimes) : (s.nu d)⁻¹ = ∑ l in 
divisors s.prodPrimes, if l ∣ d then (s.sel…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
The main sum we get from Λ² coefficients can be written as a diagonalized quadra
tic form with
  eigenvalues given by `1/selbergTerms`
-/
theorem mainSum_lambdaSquared_eq_sum_mul_sum_sq (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ l ∈ divisors s.prodPrimes, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 := by
  calc mainSum (lambdaSquared w) =
    ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes, (∑ l ∈ divisors s.prodPrimes,
      if l ∣ d1.gcd d2 then (s.selbergTerms l)⁻¹ * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0)
        := ?caseA
    _ = ∑ l ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
      if l ∣ Nat.gcd d1 d2 then (s.selbergTerms l)⁻¹ * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0
        := ?caseB
    _ = ∑ l ∈ divisors s.prodPrimes,
      (s.selbergTerms l)⁻¹ * (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2
        := ?caseC
  case caseA =>
    rw [mainSum_lambdaSquared_eq_sum_sum_mul w]
    congr! 2 with d1 hd1 d2 hd2
    have hgcd_dvd : d1.gcd d2 ∣ s.prodPrimes :=
      (Nat.gcd_dvd_left d1 d2).trans (dvd_of_mem_divisors hd1)
    simp_rw [nu_inv_eq_sum_divisors_inv_selbergTerms hgcd_dvd, ← sum_filter, mul_sum]
    congr with l
    ring
  case caseB =>
    rw [eq_comm, sum_comm, sum_congr rfl fun _ _ ↦ sum_comm]
  case caseC =>
    simp_rw [← sum_filter, sq, sum_mul, mul_sum, sum_filter, ite_sum_zero,
      ← ite_and, dvd_gcd_iff, mul_assoc]

end QuadForm

end BoundingSieve

