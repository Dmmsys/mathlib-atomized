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

/--
Definition of `BoundingSieve` / `BoundingSieve` 的定义

English:
structure BoundingSieve
  parameters: where
  axioms and operations (10):
    - support : Finset Nat
    - prodPrimes : Nat
    - prodPrimes_squarefree : Squarefree prodPrimes
    - weights : Nat -> Real
    - weights_nonneg : forall n : Nat, 0 <= weights n
    - totalMass : Real
    - nu : ArithmeticFunction Real
    - nu_mult : nu.IsMultiplicative
    - nu_pos_of_prime : forall p : Nat, p.Prime -> p ∣ prodPrimes -> 0 < nu p
    - nu_lt_one_of_prime : forall p : Nat, p.Prime -> p ∣ prodPrimes -> nu p < 1

中文:
结构 BoundingSieve
  参数: where
  公理与运算 (10 个):
    - support : 有限集 自然数
    - prodPrimes : 自然数
    - prodPrimes_squarefree : Squarefree prodPrimes
    - weights : 自然数 -> 实数
    - weights_nonneg : 对任意 n : 自然数, 0 <= weights n
    - totalMass : 实数
    - nu : ArithmeticFunction 实数
    - nu_mult : nu.是Multiplicative
    - nu_pos_of_prime : 对任意 p : 自然数, p.素 -> p ∣ prodPrimes -> 0 < nu p
    - nu_lt_one_of_prime : 对任意 p : 自然数, p.素 -> p ∣ prodPrimes -> nu p < 1
-/
structure BoundingSieve where
  /-- The set of natural numbers that is to be sifted. The fundamental lemma yields an upper bound
  on the size of this set after the multiples of small primes have been removed. -/
  support : Finset Nat
  /-- The finite set of prime numbers whose multiples are to be sifted from `support`. We work with
  their product because it lets us treat `nu` as a multiplicative arithmetic function. It also
  plays well with Moebius inversion. -/
  prodPrimes : Nat
  prodPrimes_squarefree : Squarefree prodPrimes
  /-- A sequence representing how much each element of `support` should be weighted. -/
  weights : Nat -> Real
  weights_nonneg : forall n : Nat, 0 <= weights n
  /-- An approximation to `∑ i in support, weights i`, i.e. the size of the unsifted set. A bad
  approximation will yield a weak statement in the final theorem. -/
  totalMass : Real
  /-- `nu d` is an approximation to the proportion of elements of `support` that are a multiple of
  `d` -/
  nu : ArithmeticFunction Real
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : forall p : Nat, p.Prime -> p ∣ prodPrimes -> 0 < nu p
  nu_lt_one_of_prime : forall p : Nat, p.Prime -> p ∣ prodPrimes -> nu p < 1

/--
Definition of `SelbergSieve` / `SelbergSieve` 的定义

English:
structure SelbergSieve
  parameters: extends BoundingSieve
  extends: BoundingSieve
  axioms and operations (2):
    - level : Real
    - one_le_level : 1 <= level

中文:
结构 Selberg筛
  参数: extends BoundingSieve
  继承: BoundingSieve
  公理与运算 (2 个):
    - level : 实数
    - one_le_level : 1 <= level
-/
structure SelbergSieve extends BoundingSieve where
  /-- The `level` of the sieve controls how many terms we include in the inclusion-exclusion type
  sum. A higher level will yield a tighter bound for the main term, but will also increase the
  size of the error term. -/
  level : Real
  one_le_level : 1 <= level

attribute [arith_mult] BoundingSieve.nu_mult

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `BoundingSieve.weights`. -/
@[positivity BoundingSieve.weights _ _]
meta def evalBoundingSieveWeights : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@BoundingSieve.weights $s $n) =>
    assertInstancesCommute
    pure (.nonnegative q(BoundingSieve.weights_nonneg $s $n))
  | _, _, _ => throwError "not BoundingSieve.weights"

end Mathlib.Meta.Positivity

namespace BoundingSieve
open SelbergSieve

/--
theorem `one_le_y` / 定理 `one_le_y`

English:
theorem one_le_y
  given: {s : SelbergSieve}
  statement: 1 <= s.level
  proof: s.one_le_level

中文:
定理 one_le_y
  条件: {s : Selberg筛}
  结论: 1 <= s.level
  证明: s.one_le_level

Depends on / 依赖: one_le_level, s.one_le_level
-/
theorem one_le_y {s : SelbergSieve} : 1 <= s.level := s.one_le_level

variable {s : BoundingSieve}


/--
theorem `prodPrimes_ne_zero` / 定理 `prodPrimes_ne_zero`

English:
theorem prodPrimes_ne_zero
  statement: s.prodPrimes != 0
  proof: Squarefree.ne_zero s.prodPrimes_squarefree

中文:
定理 prodPrimes_ne_zero
  结论: s.prodPrimes != 0
  证明: Squarefree.ne_zero s.prodPrimes_squarefree

Depends on / 依赖: Squarefree, Squarefree.ne_zero, ne_zero, prodPrimes_squarefree, s.prodPrimes_squarefree
-/
theorem prodPrimes_ne_zero : s.prodPrimes != 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree

/--
theorem `squarefree_of_dvd_prodPrimes` / 定理 `squarefree_of_dvd_prodPrimes`

English:
theorem squarefree_of_dvd_prodPrimes
  given: {d : Nat} (hd : d ∣ s.prodPrimes)
  statement: Squarefree d
  proof: Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

中文:
定理 squarefree_of_dvd_prodPrimes
  条件: {d : 自然数} (hd : d ∣ s.prodPrimes)
  结论: Squarefree d
  证明: Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

Depends on / 依赖: Squarefree, Squarefree.squarefree_of_dvd, prodPrimes_squarefree, s.prodPrimes_squarefree, squarefree_of_dvd
-/
theorem squarefree_of_dvd_prodPrimes {d : Nat} (hd : d ∣ s.prodPrimes) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

/--
theorem `squarefree_of_mem_divisors_prodPrimes` / 定理 `squarefree_of_mem_divisors_prodPrimes`

English:
theorem squarefree_of_mem_divisors_prodPrimes
  given: {d : Nat} (hd : d in divisors s.prodPrimes)
  proof: by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

中文:
定理 squarefree_of_mem_divisors_prodPrimes
  条件: {d : 自然数} (hd : d in divisors s.prodPrimes)
  证明: by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

Depends on / 依赖: MeasureTheory, MeasureTheory.nonempty_of_measure_ne_zero, Nat.mem_divisors, Squarefree, Squarefree.squarefree_of_dvd, Subsingleton, Subsingleton.mem_iff_nonempty.mpr, hd.left, id_apply, mem_divisors, mem_iff_nonempty, ne_of_lt, nonempty_of_measure_ne_zero, prodPrimes_squarefree, s.prodPrimes_squarefree, squarefree_of_dvd
-/
theorem squarefree_of_mem_divisors_prodPrimes {d : Nat} (hd : d in divisors s.prodPrimes) :
    Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree


/--
theorem `prod_primeFactors_nu` / 定理 `prod_primeFactors_nu`

English:
theorem prod_primeFactors_nu
  given: {d : Nat} (hd : d ∣ s.prodPrimes)
  proof: by
  rw [← s.nu_mult.map_prod_of_subset_primeFactors _ _ subset_rfl]; rw [Nat.prod_primeFactors_of_squarefree Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree]

中文:
定理 prod_primeFactors_nu
  条件: {d : 自然数} (hd : d ∣ s.prodPrimes)
  证明: by
  rw [← s.nu_mult.map_prod_of_subset_primeFactors _ _ subset_rfl]; rw [Nat.prod_primeFactors_of_squarefree Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree]

Depends on / 依赖: Nat.prod_primeFactors_of_squarefree, Squarefree, Squarefree.squarefree_of_dvd, irreducible, map_prod_of_subset_primeFactors, nu_mult, prodPrimes_squarefree, prod_primeFactors_of_squarefree, s.nu_mult.map_prod_of_subset_primeFactors, s.prodPrimes_squarefree, squarefree_of_dvd, subset_rfl
-/
theorem prod_primeFactors_nu {d : Nat} (hd : d ∣ s.prodPrimes) :
    ∏ p in d.primeFactors, s.nu p = s.nu d := by
  rw [← s.nu_mult.map_prod_of_subset_primeFactors _ _ subset_rfl]; rw [Nat.prod_primeFactors_of_squarefree Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree]

/--
theorem `nu_pos_of_dvd_prodPrimes` / 定理 `nu_pos_of_dvd_prodPrimes`

English:
theorem nu_pos_of_dvd_prodPrimes
  given: {d : Nat} (hd : d ∣ s.prodPrimes)
  statement: 0 < s.nu d
  proof: by
  calc
    0 < ∏ p in d.primeFactors, s.nu p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ s.prodPrimes := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = s.nu d :=

中文:
定理 nu_pos_of_dvd_prodPrimes
  条件: {d : 自然数} (hd : d ∣ s.prodPrimes)
  结论: 0 < s.nu d
  证明: by
  calc
    0 < ∏ p in d.primeFactors, s.nu p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ s.prodPrimes := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = s.nu d :=

Depends on / 依赖: d.primeFactors, dvd_of_mem_primeFactors, hp_dvd, hp_prime, nu_pos_of_prime, p.Prime, primeFactors, prime_of_mem_primeFactors, prodPrimes, prod_pos, prod_primeFactors_nu, s.nu, s.nu_pos_of_prime, s.prodPrimes
-/
theorem nu_pos_of_dvd_prodPrimes {d : Nat} (hd : d ∣ s.prodPrimes) : 0 < s.nu d := by
  calc
    0 < ∏ p in d.primeFactors, s.nu p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ s.prodPrimes := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = s.nu d := prod_primeFactors_nu hd

/--
theorem `nu_ne_zero` / 定理 `nu_ne_zero`

English:
theorem nu_ne_zero
  given: {d : Nat} (hd : d ∣ s.prodPrimes)
  statement: s.nu d != 0
  proof: by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes hd

中文:
定理 nu_ne_zero
  条件: {d : 自然数} (hd : d ∣ s.prodPrimes)
  结论: s.nu d != 0
  证明: by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes hd

Depends on / 依赖: _root_, _root_.ne_of_gt, ne_of_gt, nu_pos_of_dvd_prodPrimes
-/
theorem nu_ne_zero {d : Nat} (hd : d ∣ s.prodPrimes) : s.nu d != 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes hd

/--
theorem `nu_lt_one_of_dvd_prodPrimes` / 定理 `nu_lt_one_of_dvd_prodPrimes`

English:
theorem nu_lt_one_of_dvd_prodPrimes
  given: {d : Nat} (hdP : d ∣ s.prodPrimes) (hd_ne_one : d != 1)
  proof: by
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  have := hd_sq.ne_zero
  calc
    s.nu d = ∏ p in d.primeFactors, s.nu p := (prod_primeFactors_nu hdP).symm
    _ < ∏ p in d.primeFactors, 1 := by
      apply prod_lt_prod_of_nonempty
      · intro p hp
     

中文:
定理 nu_lt_one_of_dvd_prodPrimes
  条件: {d : 自然数} (hdP : d ∣ s.prodPrimes) (hd_ne_one : d != 1)
  证明: by
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  have := hd_sq.ne_zero
  calc
    s.nu d = ∏ p in d.primeFactors, s.nu p := (prod_primeFactors_nu hdP).symm
    _ < ∏ p in d.primeFactors, 1 := by
      apply prod_lt_prod_of_nonempty
      · intro p hp
     

Depends on / 依赖: Squarefree, Squarefree.squarefree_of_dvd, d.primeFactors, hd_sq, hd_sq.ne_zero, hpd.left, mem_primeFactors, mem_primeFactors_of_ne_zero, ne_zero, nonempty, nu_lt_one_of_prime, nu_pos_of_prime, primeFactors, prodPrimes_squarefree, prod_lt_prod_of_nonempty, prod_primeFactors_nu, s.nu, s.nu_lt_one_of_prime, s.nu_pos_of_prime, s.prodPrimes_squarefree
-/
theorem nu_lt_one_of_dvd_prodPrimes {d : Nat} (hdP : d ∣ s.prodPrimes) (hd_ne_one : d != 1) :
    s.nu d < 1 := by
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  have := hd_sq.ne_zero
  calc
    s.nu d = ∏ p in d.primeFactors, s.nu p := (prod_primeFactors_nu hdP).symm
    _ < ∏ p in d.primeFactors, 1 := by
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
/--
Definition of `multSum` / `multSum` 的定义

English:
definition multSum
  signature: (d : Nat)
  body: ∑ n in s.support, if d ∣ n then s.weights n else 0

中文:
定义 multSum
  签名: (d : 自然数)
  定义体: ∑ n in s.support, if d ∣ n then s.weights n else 0

Depends on / 依赖: s.support, s.weights, support, weights
-/
def multSum (d : Nat) : Real := ∑ n in s.support, if d ∣ n then s.weights n else 0


/-- The remainder term in the approximation A_d = ν (d) X + R_d. This is the degree to which `nu`
  fails to approximate the proportion of the weight that is a multiple of `d`. -/
@[simp]
/--
Definition of `rem` / `rem` 的定义

English:
definition rem
  signature: (d : Nat)
  body: s.multSum d - s.nu d * s.totalMass

中文:
定义 rem
  签名: (d : 自然数)
  定义体: s.multSum d - s.nu d * s.totalMass

Depends on / 依赖: multSum, s.multSum, s.nu, s.totalMass, totalMass
-/
def rem (d : Nat) : Real := s.multSum d - s.nu d * s.totalMass

/--
Definition of `siftedSum` / `siftedSum` 的定义

English:
definition siftedSum
  signature: : Real
  body: ∑ d in s.support, if Coprime s.prodPrimes d then s.weights d else 0

中文:
定义 siftedSum
  签名: : 实数
  定义体: ∑ d in s.support, if Coprime s.prodPrimes d then s.weights d else 0

Depends on / 依赖: Coprime, prodPrimes, s.prodPrimes, s.support, s.weights, support, weights
-/
def siftedSum : Real := ∑ d in s.support, if Coprime s.prodPrimes d then s.weights d else 0

/--
Definition of `mainSum` / `mainSum` 的定义

English:
definition mainSum
  signature: (muPlus : Nat -> Real)
  body: ∑ d in divisors s.prodPrimes, muPlus d * s.nu d

中文:
定义 mainSum
  签名: (muPlus : 自然数 -> 实数)
  定义体: ∑ d in divisors s.prodPrimes, muPlus d * s.nu d

Depends on / 依赖: divisors, muPlus, prodPrimes, s.nu, s.prodPrimes
-/
def mainSum (muPlus : Nat -> Real) : Real := ∑ d in divisors s.prodPrimes, muPlus d * s.nu d

/--
Definition of `errSum` / `errSum` 的定义

English:
definition errSum
  signature: (muPlus : Nat -> Real)
  body: ∑ d in divisors s.prodPrimes, |muPlus d| * |s.rem d|

中文:
定义 errSum
  签名: (muPlus : 自然数 -> 实数)
  定义体: ∑ d in divisors s.prodPrimes, |muPlus d| * |s.rem d|

Depends on / 依赖: divisors, muPlus, prodPrimes, s.prodPrimes, s.rem
-/
def errSum (muPlus : Nat -> Real) : Real := ∑ d in divisors s.prodPrimes, |muPlus d| * |s.rem d|

/--
theorem `multSum_eq_main_err` / 定理 `multSum_eq_main_err`

English:
theorem multSum_eq_main_err
  given: (d : Nat)
  statement: s.multSum d = s.nu d * s.totalMass + s.rem d
  proof: by
  rw [rem]
  ring

中文:
定理 multSum_eq_main_err
  条件: (d : 自然数)
  结论: s.multSum d = s.nu d * s.totalMass + s.rem d
  证明: by
  rw [rem]
  ring
-/
theorem multSum_eq_main_err (d : Nat) : s.multSum d = s.nu d * s.totalMass + s.rem d := by
  rw [rem]
  ring

/--
theorem `siftedSum_eq_sum_support_mul_ite` / 定理 `siftedSum_eq_sum_support_mul_ite`

English:
theorem siftedSum_eq_sum_support_mul_ite
  proof: by
  rw [siftedSum]
  simp_rw [mul_ite, mul_one, mul_zero]

omit s in

中文:
定理 siftedSum_eq_sum_support_mul_ite
  证明: by
  rw [siftedSum]
  simp_rw [mul_ite, mul_one, mul_zero]

omit s in

Depends on / 依赖: mul_ite, mul_one, mul_zero, siftedSum, simp_rw
-/
theorem siftedSum_eq_sum_support_mul_ite :
    s.siftedSum = ∑ d in s.support, s.weights d * if Nat.gcd s.prodPrimes d = 1 then 1 else 0 := by
  rw [siftedSum]
  simp_rw [mul_ite, mul_one, mul_zero]

omit s in
/--
Definition of `IsUpperMoebius` / `IsUpperMoebius` 的定义

English:
definition IsUpperMoebius
  signature: (muPlus : Nat -> Real)
  body: forall n : Nat, (if n = 1 then 1 else 0) <= ∑ d in n.divisors, muPlus d

中文:
定义 IsUpperMoebius
  签名: (muPlus : 自然数 -> 实数)
  定义体: forall n : Nat, (if n = 1 then 1 else 0) <= ∑ d in n.divisors, muPlus d

Depends on / 依赖: divisors, muPlus, n.divisors
-/
def IsUpperMoebius (muPlus : Nat -> Real) : Prop :=
  forall n : Nat, (if n = 1 then 1 else 0) <= ∑ d in n.divisors, muPlus d

/--
theorem `siftedSum_le_sum_of_upperMoebius` / 定理 `siftedSum_le_sum_of_upperMoebius`

English:
theorem siftedSum_le_sum_of_upperMoebius
  given: (muPlus : Nat -> Real) (h : IsUpperMoebius muPlus)
  proof: by
  have hμ : forall n, (if n = 1 then 1 else 0) <= ∑ d in n.divisors, muPlus d := h
  calc siftedSum <=
    ∑ n in s.support, s.weights n * ∑ d in (Nat.gcd s.prodPrimes n).divisors, muPlus d := ?caseA
    _ = ∑ n in s.support, ∑ d in divisors s.prodPrimes,
        if d ∣ n then s.weights n * muPlu

中文:
定理 siftedSum_le_sum_of_upperMoebius
  条件: (muPlus : 自然数 -> 实数) (h : IsUpperMoebius muPlus)
  证明: by
  have hμ : forall n, (if n = 1 then 1 else 0) <= ∑ d in n.divisors, muPlus d := h
  calc siftedSum <=
    ∑ n in s.support, s.weights n * ∑ d in (Nat.gcd s.prodPrimes n).divisors, muPlus d := ?caseA
    _ = ∑ n in s.support, ∑ d in divisors s.prodPrimes,
        if d ∣ n then s.weights n * muPlu

Depends on / 依赖: Nat.gcd, divisors, muPlus, mul_sum, multSum, n.divisors, prodPrimes, s.prodPrimes, s.support, s.weights, siftedSum, siftedSum_eq_sum_support_mul_ite, simp_rw, support, weights
-/
theorem siftedSum_le_sum_of_upperMoebius (muPlus : Nat -> Real) (h : IsUpperMoebius muPlus) :
    s.siftedSum <= ∑ d in divisors s.prodPrimes, muPlus d * s.multSum d := by
  have hμ : forall n, (if n = 1 then 1 else 0) <= ∑ d in n.divisors, muPlus d := h
  calc siftedSum <=
    ∑ n in s.support, s.weights n * ∑ d in (Nat.gcd s.prodPrimes n).divisors, muPlus d := ?caseA
    _ = ∑ n in s.support, ∑ d in divisors s.prodPrimes,
        if d ∣ n then s.weights n * muPlus d else 0 := ?caseB
    _ = ∑ d in divisors s.prodPrimes, muPlus d * multSum d := ?caseC
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

/--
theorem `siftedSum_le_mainSum_errSum_of_upperMoebius` / 定理 `siftedSum_le_mainSum_errSum_of_upperMoebius`

English:
theorem siftedSum_le_mainSum_errSum_of_upperMoebius
  given: (muPlus : Nat -> Real) (h : IsUpperMoebius muPlus)
  proof: calc
  s.siftedSum <= ∑ d in divisors s.prodPrimes, muPlus d * multSum d :=
    siftedSum_le_sum_of_upperMoebius _ h
  _ = s.totalMass * mainSum muPlus + ∑ d in divisors s.prodPrimes, muPlus d * s.rem d := by
    rw [mainSum]; rw [mul_sum]; rw [← sum_add_distrib]
    congr with d
    rw [rem]
    ri

中文:
定理 siftedSum_le_mainSum_errSum_of_upperMoebius
  条件: (muPlus : 自然数 -> 实数) (h : IsUpperMoebius muPlus)
  证明: calc
  s.siftedSum <= ∑ d in divisors s.prodPrimes, muPlus d * multSum d :=
    siftedSum_le_sum_of_upperMoebius _ h
  _ = s.totalMass * mainSum muPlus + ∑ d in divisors s.prodPrimes, muPlus d * s.rem d := by
    rw [mainSum]; rw [mul_sum]; rw [← sum_add_distrib]
    congr with d
    rw [rem]
    ri
-/
theorem siftedSum_le_mainSum_errSum_of_upperMoebius (muPlus : Nat -> Real) (h : IsUpperMoebius muPlus) :
    s.siftedSum <= s.totalMass * s.mainSum muPlus + s.errSum muPlus := calc
  s.siftedSum <= ∑ d in divisors s.prodPrimes, muPlus d * multSum d :=
    siftedSum_le_sum_of_upperMoebius _ h
  _ = s.totalMass * mainSum muPlus + ∑ d in divisors s.prodPrimes, muPlus d * s.rem d := by
    rw [mainSum]; rw [mul_sum]; rw [← sum_add_distrib]
    congr with d
    rw [rem]
    ring
  _ <= s.totalMass * mainSum muPlus + errSum muPlus := by
    rw [errSum]
    gcongr _ + ∑ d in _, ?_ with d
    rw [← abs_mul]
    exact le_abs_self (muPlus d * s.rem d)

section LambdaSquared

/--
Definition of `lambdaSquared` / `lambdaSquared` 的定义

English:
definition lambdaSquared
  signature: (weights : Nat -> Real)
  body: fun d =>
  ∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

中文:
定义 lambdaSquared
  签名: (weights : 自然数 -> 实数)
  定义体: fun d =>
  ∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0
-/
def lambdaSquared (weights : Nat -> Real) : Nat -> Real := fun d =>
  ∑ d1 in d.divisors, ∑ d2 in d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

/--
theorem `sum_divisors_lambda_sq_larger_sum` / 定理 `sum_divisors_lambda_sq_larger_sum`

English:
theorem sum_divisors_lambda_sq_larger_sum
  given: (f : Nat -> Nat -> Nat -> Real) (n : Nat)
  proof: by
  congr! 1 with d hd
  rw [mem_divisors] at hd
  suffices forall d1 d2, (d1 ∣ d ∧ d2 ∣ d ∧ d = d1.lcm d2) = (d = d1.lcm d2) by
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ite_sum_zero, ← ite_and, this]
  simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]

中文:
定理 sum_divisors_lambda_sq_larger_sum
  条件: (f : 自然数 -> 自然数 -> 自然数 -> 实数) (n : 自然数)
  证明: by
  congr! 1 with d hd
  rw [mem_divisors] at hd
  suffices forall d1 d2, (d1 ∣ d ∧ d2 ∣ d ∧ d = d1.lcm d2) = (d = d1.lcm d2) by
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ite_sum_zero, ← ite_and, this]
  simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
-/
private theorem sum_divisors_lambda_sq_larger_sum (f : Nat -> Nat -> Nat -> Real) (n : Nat) :
    (∑ d in n.divisors, ∑ d1 in d.divisors, ∑ d2 in d.divisors,
      if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
    (∑ d in n.divisors, ∑ d1 in n.divisors, ∑ d2 in n.divisors,
     if d = Nat.lcm d1 d2 then f d1 d2 d else 0) := by
  congr! 1 with d hd
  rw [mem_divisors] at hd
  suffices forall d1 d2, (d1 ∣ d ∧ d2 ∣ d ∧ d = d1.lcm d2) = (d = d1.lcm d2) by
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ite_sum_zero, ← ite_and, this]
  simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]

/--
theorem `upperMoebius_lambdaSquared` / 定理 `upperMoebius_lambdaSquared`

English:
theorem upperMoebius_lambdaSquared
  given: (weights : Nat -> Real) (hw : weights 1 = 1)
  proof: by
  dsimp only [IsUpperMoebius, lambdaSquared]
  intro n
  split_ifs
  · simp_all
  grw [sq_nonneg (∑ d in n.divisors, weights d), sum_divisors_lambda_sq_larger_sum _ n, sum_comm]
  apply le_of_eq
  simp_rw [sq, mul_sum, sum_mul]
  congr! 1 with d1 hd1
  rw [sum_comm]
  congr! 1 with d2 hd2
  rw [s

中文:
定理 upperMoebius_lambdaSquared
  条件: (weights : 自然数 -> 实数) (hw : weights 1 = 1)
  证明: by
  dsimp only [IsUpperMoebius, lambdaSquared]
  intro n
  split_ifs
  · simp_all
  grw [sq_nonneg (∑ d in n.divisors, weights d), sum_divisors_lambda_sq_larger_sum _ n, sum_comm]
  apply le_of_eq
  simp_rw [sq, mul_sum, sum_mul]
  congr! 1 with d1 hd1
  rw [sum_comm]
  congr! 1 with d2 hd2
  rw [s

Depends on / 依赖: IsUpperMoebius, divisors, lambdaSquared, le_of_eq, mul_comm, mul_sum, n.divisors, simp_rw, split_ifs, sq_nonneg, sum_comm, sum_divisors_lambda_sq_larger_sum, sum_ite_eq_of_mem, sum_mul, weights
-/
theorem upperMoebius_lambdaSquared (weights : Nat -> Real) (hw : weights 1 = 1) :
IsUpperMoebius lambdaSquared weights := by
  dsimp only [IsUpperMoebius, lambdaSquared]
  intro n
  split_ifs
  · simp_all
  grw [sq_nonneg (∑ d in n.divisors, weights d), sum_divisors_lambda_sq_larger_sum _ n, sum_comm]
  apply le_of_eq
  simp_rw [sq, mul_sum, sum_mul]
  congr! 1 with d1 hd1
  rw [sum_comm]
  congr! 1 with d2 hd2
  rw [sum_ite_eq_of_mem']; rw [mul_comm]
  -- Deal with the side goal from `sum_ite_eq_of_mem'`
  rw [mem_divisors]; rw [Nat.lcm_dvd_iff]
  exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩

end LambdaSquared

section SelbergTerms

variable {s : BoundingSieve}

/--
Definition of `selbergTerms` / `selbergTerms` 的定义

English:
definition selbergTerms
  signature: : ArithmeticFunction Real
  body: s.nu.pmul (.prodPrimeFactors fun p => (1 - s.nu p)⁻¹)

中文:
定义 selbergTerms
  签名: : ArithmeticFunction 实数
  定义体: s.nu.pmul (.prodPrimeFactors fun p => (1 - s.nu p)⁻¹)

Depends on / 依赖: prodPrimeFactors, s.nu, s.nu.pmul
-/
def selbergTerms : ArithmeticFunction Real :=
  s.nu.pmul (.prodPrimeFactors fun p => (1 - s.nu p)⁻¹)

/--
theorem `selbergTerms_apply` / 定理 `selbergTerms_apply`

English:
theorem selbergTerms_apply
  given: (d : Nat)
  proof: by
  unfold selbergTerms
  by_cases h : d = 0
  · simp [h]
  rw [ArithmeticFunction.pmul_apply]; rw [ArithmeticFunction.prodPrimeFactors_apply h]

中文:
定理 selbergTerms_apply
  条件: (d : 自然数)
  证明: by
  unfold selbergTerms
  by_cases h : d = 0
  · simp [h]
  rw [ArithmeticFunction.pmul_apply]; rw [ArithmeticFunction.prodPrimeFactors_apply h]

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply, pmul_apply, prodPrimeFactors_apply, selbergTerms
-/
theorem selbergTerms_apply (d : Nat) :
    s.selbergTerms d = s.nu d * ∏ p in d.primeFactors, (1 - s.nu p)⁻¹ := by
  unfold selbergTerms
  by_cases h : d = 0
  · simp [h]
  rw [ArithmeticFunction.pmul_apply]; rw [ArithmeticFunction.prodPrimeFactors_apply h]


/--
theorem `selbergTerms_pos` / 定理 `selbergTerms_pos`

English:
theorem selbergTerms_pos
  given: {l : Nat} (hl : l ∣ s.prodPrimes)
  statement: 0 < s.selbergTerms l
  proof: by
  rw [selbergTerms_apply]
refine mul_pos (nu_pos_of_dvd_prodPrimes hl) prod_pos fun p hp => ?_
  rw [inv_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp

中文:
定理 selbergTerms_pos
  条件: {l : 自然数} (hl : l ∣ s.prodPrimes)
  结论: 0 < s.selbergTerms l
  证明: by
  rw [selbergTerms_apply]
refine mul_pos (nu_pos_of_dvd_prodPrimes hl) prod_pos fun p hp => ?_
  rw [inv_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp

Depends on / 依赖: Nat.dvd_of_mem_primeFactors, dvd_of_mem_primeFactors, hp_dvd, hp_prime, inv_pos, mul_pos, nu_lt_one_of_prime, nu_pos_of_dvd_prodPrimes, p.Prime, prime_of_mem_primeFactors, prodPrimes, prod_pos, s.nu_lt_one_of_prime, s.prodPrimes, selbergTerms_apply
-/
theorem selbergTerms_pos {l : Nat} (hl : l ∣ s.prodPrimes) : 0 < s.selbergTerms l := by
  rw [selbergTerms_apply]
refine mul_pos (nu_pos_of_dvd_prodPrimes hl) prod_pos fun p hp => ?_
  rw [inv_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

/--
theorem `selbergTerms_isMultiplicative` / 定理 `selbergTerms_isMultiplicative`

English:
theorem selbergTerms_isMultiplicative
  statement: ArithmeticFunction.IsMultiplicative s.selbergTerms
  proof: by
  unfold selbergTerms
  arith_mult

中文:
定理 selbergTerms_isMultiplicative
  结论: ArithmeticFunction.是Multiplicative s.selbergTerms
  证明: by
  unfold selbergTerms
  arith_mult

Depends on / 依赖: arith_mult, selbergTerms
-/
theorem selbergTerms_isMultiplicative : ArithmeticFunction.IsMultiplicative s.selbergTerms := by
  unfold selbergTerms
  arith_mult

/--
theorem `inv_selbergTerms_eq_sum_divisors_moebius_nu` / 定理 `inv_selbergTerms_eq_sum_divisors_moebius_nu`

English:
theorem inv_selbergTerms_eq_sum_divisors_moebius_nu
  statement: {l : Nat} (hl : Squarefree l)
  proof: by
  simp only [selbergTerms_apply, mul_inv, inv_inv,
    Finset.prod_inv_distrib, s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ hl, mul_sum]
  rw [← Nat.sum_divisorsAntidiagonal fun i _ : Nat => (s.nu l)⁻¹ * (↑(μ i) * s.nu i)]
  congr! 1 with ⟨d, e⟩ hd
  obtain ⟨rfl, -⟩ : d * e = l ∧ _ := by s

中文:
定理 inv_selbergTerms_eq_sum_divisors_moebius_nu
  结论: {l : 自然数} (hl : Squarefree l)
  证明: by
  simp only [selbergTerms_apply, mul_inv, inv_inv,
    Finset.prod_inv_distrib, s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ hl, mul_sum]
  rw [← Nat.sum_divisorsAntidiagonal fun i _ : Nat => (s.nu l)⁻¹ * (↑(μ i) * s.nu i)]
  congr! 1 with ⟨d, e⟩ hd
  obtain ⟨rfl, -⟩ : d * e = l ∧ _ := by s

Depends on / 依赖: Coprime, Finset, Finset.prod_inv_distrib, Nat.sum_divisorsAntidiagonal, d.Coprime, inv_inv, map_mul_of_coprime, mul_inv, mul_sum, nu_mul, nu_mult, prodPrimeFactors_one_sub_of_squarefree, prod_inv_distrib, s.nu, s.nu_mul, s.nu_mult.map_mul_of_coprime, s.nu_mult.prodPrimeFactors_one_sub_of_squarefree, selbergTerms_apply, squarefree_mul_iff, sum_divisorsAntidiagonal
-/
theorem inv_selbergTerms_eq_sum_divisors_moebius_nu {l : Nat} (hl : Squarefree l)
    (hnu_nonzero : s.nu l != 0) :
    (s.selbergTerms l)⁻¹ = ∑ ⟨d, e⟩ in l.divisorsAntidiagonal, (μ d) * (s.nu e)⁻¹ := by
  simp only [selbergTerms_apply, mul_inv, inv_inv,
    Finset.prod_inv_distrib, s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ hl, mul_sum]
  rw [← Nat.sum_divisorsAntidiagonal fun i _ : Nat => (s.nu l)⁻¹ * (↑(μ i) * s.nu i)]
  congr! 1 with ⟨d, e⟩ hd
  obtain ⟨rfl, -⟩ : d * e = l ∧ _ := by simpa using hd
  obtain ⟨hde, -⟩ : d.Coprime e ∧ _ := by simpa only [squarefree_mul_iff] using hl
  obtain ⟨hd0, he0⟩ : ¬s.nu d = 0 ∧ ¬s.nu e = 0 := by simp_all [s.nu_mult.map_mul_of_coprime hde]
  simp [field, s.nu_mult.map_mul_of_coprime hde, mul_assoc]

/--
theorem `nu_inv_eq_sum_divisors_inv_selbergTerms` / 定理 `nu_inv_eq_sum_divisors_inv_selbergTerms`

English:
theorem nu_inv_eq_sum_divisors_inv_selbergTerms
  given: {d : Nat} (hdP : d ∣ s.prodPrimes)
  proof: by
  rw [eq_comm]; rw [← sum_filter]; rw [Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
have hd_pos : 0 < d := Nat.pos_of_ne_zero ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).m

中文:
定理 nu_inv_eq_sum_divisors_inv_selbergTerms
  条件: {d : 自然数} (hdP : d ∣ s.prodPrimes)
  证明: by
  rw [eq_comm]; rw [← sum_filter]; rw [Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
have hd_pos : 0 < d := Nat.pos_of_ne_zero ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).m

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on, Nat.divisors_filter_dvd_of_dvd, Nat.dvd_trans, Nat.pos_of_ne_zero, Squarefree, Squarefree.squarefree_of_dvd, divisors_filter_dvd_of_dvd, dvd_trans, eq_comm, hd_pos, inv_selbergTerms_eq_sum_divisors_moebius_nu, ne_of_gt, ne_zero_of_dvd_ne_zero, nu_pos_of_dvd_prodPrimes, pos_of_ne_zero, prodPrimes_ne_zero, prodPrimes_squarefree, revert, s.prodPrimes_squarefree
-/
theorem nu_inv_eq_sum_divisors_inv_selbergTerms {d : Nat} (hdP : d ∣ s.prodPrimes) :
    (s.nu d)⁻¹ = ∑ l in divisors s.prodPrimes, if l ∣ d then (s.selbergTerms l)⁻¹ else 0 := by
  rw [eq_comm]; rw [← sum_filter]; rw [Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
have hd_pos : 0 < d := Nat.pos_of_ne_zero ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  exact inv_selbergTerms_eq_sum_divisors_moebius_nu
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
.symm (ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP)

/--
theorem `sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv` / 定理 `sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv`

English:
theorem sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv
  given: {d : Nat} (hd : d ∣ s.prodPrimes)
  proof: by
  calc
    (∑ l in divisors s.prodPrimes, if l ∣ d then s.selbergTerms l else 0) =
        ∑ l in divisors s.prodPrimes, if l ∣ d then s.selbergTerms (d / l) else 0 := by
      simp_rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hd,
        sum_div_divisors d s.selbergTerms]


中文:
定理 sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv
  条件: {d : 自然数} (hd : d ∣ s.prodPrimes)
  证明: by
  calc
    (∑ l in divisors s.prodPrimes, if l ∣ d then s.selbergTerms l else 0) =
        ∑ l in divisors s.prodPrimes, if l ∣ d then s.selbergTerms (d / l) else 0 := by
      simp_rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hd,
        sum_div_divisors d s.selbergTerms]


Depends on / 依赖: Nat.divisors_filter_dvd_of_dvd, divisors, divisors_filter_dvd_of_dvd, mem_divisors, mem_filter, mul_sum, ne_eq, prodPrimes, prodPrimes_ne_zero, s.prodPrimes, s.selbergTerms, selbergTerms, selbergTerms_isMultipl, simp_rw, sum_div_divisors, sum_filter
-/
theorem sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv {d : Nat} (hd : d ∣ s.prodPrimes) :
    (∑ l in divisors s.prodPrimes, if l ∣ d then s.selbergTerms l else 0) =
      s.selbergTerms d * (s.nu d)⁻¹ := by
  calc
    (∑ l in divisors s.prodPrimes, if l ∣ d then s.selbergTerms l else 0) =
        ∑ l in divisors s.prodPrimes, if l ∣ d then s.selbergTerms (d / l) else 0 := by
      simp_rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hd,
        sum_div_divisors d s.selbergTerms]
    _ = s.selbergTerms d *
          ∑ l in divisors s.prodPrimes, if l ∣ d then (s.selbergTerms l)⁻¹ else 0 := by
      simp_rw [← sum_filter, mul_sum]
      congr! 1 with l hl
      simp only [mem_filter, mem_divisors, ne_eq] at hl
      rw [selbergTerms_isMultiplicative.map_div_of_coprime hl.2]
      · ring
· apply coprime_of_squarefree_mul
          (Nat.div_mul_cancel hl.2).symm ▸ (squarefree_of_dvd_prodPrimes hd)
      · exact (selbergTerms_pos hl.1.1).ne'
    _ = s.selbergTerms d * (s.nu d)⁻¹ := by rw [← nu_inv_eq_sum_divisors_inv_selbergTerms hd]

end SelbergTerms

section QuadForm

/--
theorem `mainSum_lambdaSquared_eq_sum_sum_mul` / 定理 `mainSum_lambdaSquared_eq_sum_sum_mul`

English:
theorem mainSum_lambdaSquared_eq_sum_sum_mul
  given: (w : Nat -> Real)
  proof: by
  calc mainSum (lambdaSquared w)
      = ∑ d in divisors s.prodPrimes, ∑ d1 in divisors d, ∑ d2 in divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := ?caseA
    _ = ∑ d in divisors s.prodPrimes, ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes,
          if d =

中文:
定理 mainSum_lambdaSquared_eq_sum_sum_mul
  条件: (w : 自然数 -> 实数)
  证明: by
  calc mainSum (lambdaSquared w)
      = ∑ d in divisors s.prodPrimes, ∑ d1 in divisors d, ∑ d2 in divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := ?caseA
    _ = ∑ d in divisors s.prodPrimes, ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes,
          if d =

Depends on / 依赖: d1.gcd, d1.lcm, divisors, lambdaSquared, mainSum, prodPrimes, s.nu, s.prodPrimes, sum_divisors_lambda_sq_larger_sum
-/
theorem mainSum_lambdaSquared_eq_sum_sum_mul (w : Nat -> Real) :
    s.mainSum (lambdaSquared w) =
      ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes,
        s.nu d1 * w d1 * s.nu d2 * w d2 * (s.nu (d1.gcd d2))⁻¹ := by
  calc mainSum (lambdaSquared w)
      = ∑ d in divisors s.prodPrimes, ∑ d1 in divisors d, ∑ d2 in divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := ?caseA
    _ = ∑ d in divisors s.prodPrimes, ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := sum_divisors_lambda_sq_larger_sum _ _
    _ = ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes,
          s.nu d1 * w d1 * s.nu d2 * w d2 * (s.nu (d1.gcd d2))⁻¹ := ?caseB
  case caseA =>
    simp [mainSum, lambdaSquared, sum_mul]
  case caseB =>
    rw [sum_comm]; rw [sum_congr rfl]; intro d1 hd1
    rw [sum_comm]; rw [sum_congr rfl]; intro d2 hd2
    have h : d1.lcm d2 ∣ s.prodPrimes :=
      Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
    rw [sum_ite_eq_of_mem' (divisors s.prodPrimes) (d1.lcm d2) _
      (mem_divisors.mpr ⟨h]; rw [prodPrimes_ne_zero⟩)]; rw [s.nu_mult.map_lcm]
    · ring
    refine (nu_pos_of_dvd_prodPrimes ?_).ne'
    exact (Nat.gcd_dvd_left d1 d2).trans (dvd_of_mem_divisors hd1)

/--
theorem `mainSum_lambdaSquared_eq_sum_mul_sum_sq` / 定理 `mainSum_lambdaSquared_eq_sum_mul_sum_sq`

English:
theorem mainSum_lambdaSquared_eq_sum_mul_sum_sq
  given: (w : Nat -> Real)
  proof: by
  calc mainSum (lambdaSquared w) =
    ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes, (∑ l in divisors s.prodPrimes,
      if l ∣ d1.gcd d2 then (s.selbergTerms l)⁻¹ * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0)
        := ?caseA
    _ = ∑ l in divisors s.prodPrimes, ∑ d1 in diviso

中文:
定理 mainSum_lambdaSquared_eq_sum_mul_sum_sq
  条件: (w : 自然数 -> 实数)
  证明: by
  calc mainSum (lambdaSquared w) =
    ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes, (∑ l in divisors s.prodPrimes,
      if l ∣ d1.gcd d2 then (s.selbergTerms l)⁻¹ * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0)
        := ?caseA
    _ = ∑ l in divisors s.prodPrimes, ∑ d1 in diviso

Depends on / 依赖: Nat.gcd, d1.gcd, divisors, lambdaSquared, mainSum, prodPrimes, s.nu, s.prodPrimes, s.selbergTerms, selbergTerms
-/
theorem mainSum_lambdaSquared_eq_sum_mul_sum_sq (w : Nat -> Real) :
    s.mainSum (lambdaSquared w) =
      ∑ l in divisors s.prodPrimes, (s.selbergTerms l)⁻¹ *
        (∑ d in divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 := by
  calc mainSum (lambdaSquared w) =
    ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes, (∑ l in divisors s.prodPrimes,
      if l ∣ d1.gcd d2 then (s.selbergTerms l)⁻¹ * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0)
        := ?caseA
    _ = ∑ l in divisors s.prodPrimes, ∑ d1 in divisors s.prodPrimes, ∑ d2 in divisors s.prodPrimes,
      if l ∣ Nat.gcd d1 d2 then (s.selbergTerms l)⁻¹ * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0
        := ?caseB
    _ = ∑ l in divisors s.prodPrimes,
      (s.selbergTerms l)⁻¹ * (∑ d in divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2
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
    rw [eq_comm]; rw [sum_comm]; rw [sum_congr rfl fun _ _ => sum_comm]
  case caseC =>
    simp_rw [← sum_filter, sq, sum_mul, mul_sum, sum_filter, ite_sum_zero,
      ← ite_and, dvd_gcd_iff, mul_assoc]

end QuadForm

end BoundingSieve
