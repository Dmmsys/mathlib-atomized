/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Euler Products

The main result in this file is `EulerProduct.eulerProduct_hasProd`, which says that
if `f : ℕ → R` is norm-summable, where `R` is a complete normed commutative ring and `f` is
multiplicative on coprime arguments with `f 0 = 0`, then
`∏' p : Primes, ∑' e : ℕ, f (p^e)` converges to `∑' n, f n`.

`ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd` is a version
for multiplicative arithmetic functions in the sense of
`ArithmeticFunction.IsMultiplicative`.

There is also a version `EulerProduct.eulerProduct_completely_multiplicative_hasProd`,
which states that `∏' p : Primes, (1 - f p)⁻¹` converges to `∑' n, f n`
when `f` is completely multiplicative with values in a complete normed field `F`
(implemented as `f : ℕ →*₀ F`).

There are variants stating the equality of the infinite product and the infinite sum
(`EulerProduct.eulerProduct_tprod`, `ArithmeticFunction.IsMultiplicative.eulerProduct_tprod`,
`EulerProduct.eulerProduct_completely_multiplicative_tprod`) and also variants stating
the convergence of the sequence of partial products over primes `< n`
(`EulerProduct.eulerProduct`, `ArithmeticFunction.IsMultiplicative.eulerProduct`,
`EulerProduct.eulerProduct_completely_multiplicative`.)

An intermediate step is `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
(and its variant `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric`),
which relates the finite product over primes `p ∈ s` to the sum of `f n` over `s`-factored `n`,
for `s : Finset ℕ`.

## Tags

Euler product, multiplicative function
-/

public section

/--
lemma `Summable.norm_lt_one` / 引理 `Summable.norm_lt_one`

English:
lemma Summable.norm_lt_one
  statement: {F : Type*} [NormedDivisionRing F] [CompleteSpace F] {f : Nat ->* F}
  proof: by
  refine summable_geometric_iff_norm_lt_one.mp ?_
  simp_rw [← map_pow]
exact hsum.comp_injective Nat.pow_right_injective hp

中文:
引理 Summable.norm_lt_one
  结论: {F : 类型} [NormedDivisionRing F] [CompleteSpace F] {f : 自然数 ->* F}
  证明: by
  refine summable_geometric_iff_norm_lt_one.mp ?_
  simp_rw [← map_pow]
exact hsum.comp_injective Nat.pow_right_injective hp

Depends on / 依赖: Nat.pow_right_injective, comp_injective, hsum.comp_injective, map_pow, pow_right_injective, simp_rw, summable_geometric_iff_norm_lt_one, summable_geometric_iff_norm_lt_one.mp
-/
lemma Summable.norm_lt_one {F : Type*} [NormedDivisionRing F] [CompleteSpace F] {f : Nat ->* F}
    (hsum : Summable f) {p : Nat} (hp : 1 < p) :
    ‖f p‖ < 1 := by
  refine summable_geometric_iff_norm_lt_one.mp ?_
  simp_rw [← map_pow]
exact hsum.comp_injective Nat.pow_right_injective hp

open scoped Topology

open Nat Finset

section General

/-!
### General Euler Products

In this section we consider multiplicative (on coprime arguments) functions `f : ℕ → R`,
where `R` is a complete normed commutative ring. The main result is `EulerProduct.eulerProduct`.
-/

variable {R : Type*} [NormedCommRing R] {f : Nat -> R}

-- local instance to speed up typeclass search
/--
lemma `instT0Space` / 引理 `instT0Space`

English:
lemma instT0Space
  statement: T0Space R
  proof: MetricSpace.instT0Space

中文:
引理 instT0Space
  结论: T0Space R
  证明: MetricSpace.instT0Space
-/
@[local instance] private lemma instT0Space : T0Space R := MetricSpace.instT0Space

variable [CompleteSpace R]

namespace EulerProduct

variable (hf₁ : f 1 = 1) (hmul : forall {m n}, Nat.Coprime m n -> f (m * n) = f m * f n)

include hf₁ hmul in
/--
lemma `summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum` / 引理 `summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`

English:
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
  proof: by
  induction s using Finset.induction with
  | empty =>
    rw [factoredNumbers_empty]
    simp only [notMem_empty, IsEmpty.forall_iff, forall_const, filter_true_of_mem, prod_empty]
    exact ⟨(Set.finite_singleton 1).summable (‖f ·‖), hf₁ ▸ hasSum_singleton 1 f⟩
  | insert p s hp ih =>
    rw [fi

中文:
引理 summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
  证明: by
  induction s using Finset.induction with
  | empty =>
    rw [factoredNumbers_empty]
    simp only [notMem_empty, IsEmpty.forall_iff, forall_const, filter_true_of_mem, prod_empty]
    exact ⟨(Set.finite_singleton 1).summable (‖f ·‖), hf₁ ▸ hasSum_singleton 1 f⟩
  | insert p s hp ih =>
    rw [fi

Depends on / 依赖: Finset, Finset.induction, Function, Function.comp_def, IsEmpty, IsEmpty.forall_iff, Set.finite_singleton, comp_def, equivProdNatFactoredNumbers, equivProdNatFactoredNumbers_apply, factoredNumbers, factoredNumbers.map_prime_pow_mul, factoredNumbers_empty, filter_insert, filter_true_of_mem, finite_singleton, forall_const, forall_iff, hasSum_singleton, insert
-/
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (hsum : forall {p : Nat}, p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)) (s : Finset Nat) :
    Summable (fun m : factoredNumbers s => ‖f m‖) ∧
      HasSum (fun m : factoredNumbers s => f m)
        (∏ p in s with p.Prime, ∑' n : Nat, f (p ^ n)) := by
  induction s using Finset.induction with
  | empty =>
    rw [factoredNumbers_empty]
    simp only [notMem_empty, IsEmpty.forall_iff, forall_const, filter_true_of_mem, prod_empty]
    exact ⟨(Set.finite_singleton 1).summable (‖f ·‖), hf₁ ▸ hasSum_singleton 1 f⟩
  | insert p s hp ih =>
    rw [filter_insert]
    split_ifs with hpp
    · constructor
      · simp only [← (equivProdNatFactoredNumbers hpp hp).summable_iff, Function.comp_def,
          equivProdNatFactoredNumbers_apply', factoredNumbers.map_prime_pow_mul hmul hpp hp]
        refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_mul_le ..) ?_
        apply Summable.mul_of_nonneg (hsum hpp) ih.1 <;> exact fun n => norm_nonneg _
      · have hp' : p ∉ {p in s | p.Prime} := mt (mem_of_mem_filter p) hp
        rw [prod_insert hp']; rw [← (equivProdNatFactoredNumbers hpp hp).hasSum_iff]; rw [Function.comp_def]
        conv =>
          enter [1, x]
          rw [equivProdNatFactoredNumbers_apply']; rw [factoredNumbers.map_prime_pow_mul hmul hpp hp]
        have : T3Space R := instT3Space -- speeds up the following
        apply (hsum hpp).of_norm.hasSum.mul ih.2
        -- `exact summable_mul_of_summable_norm (hsum hpp) ih.1` gives a time-out
        apply summable_mul_of_summable_norm (hsum hpp) ih.1
    · rwa [factoredNumbers_insert s hpp]

include hf₁ hmul in
/--
lemma `prod_filter_prime_tsum_eq_tsum_factoredNumbers` / 引理 `prod_filter_prime_tsum_eq_tsum_factoredNumbers`

English:
lemma prod_filter_prime_tsum_eq_tsum_factoredNumbers
  given: (hsum : Summable (‖f ·‖)) (s : Finset Nat)
  proof: (summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul
    (fun hp => hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

中文:
引理 prod_filter_prime_tsum_eq_tsum_factoredNumbers
  条件: (hsum : Summable (‖f ·‖)) (s : Finset 自然数)
  证明: (summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul
    (fun hp => hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

Depends on / 依赖: Nat.pow_right_injective, comp_injective, hp.one_lt, hsum.comp_injective, one_lt, pow_right_injective, summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum, tsum_eq, tsum_eq.symm
-/
lemma prod_filter_prime_tsum_eq_tsum_factoredNumbers (hsum : Summable (‖f ·‖)) (s : Finset Nat) :
    ∏ p in s with p.Prime, ∑' n : Nat, f (p ^ n) = ∑' m : factoredNumbers s, f m :=
  (summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul
    (fun hp => hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

/--
lemma `norm_tsum_factoredNumbers_sub_tsum_lt` / 引理 `norm_tsum_factoredNumbers_sub_tsum_lt`

English:
lemma norm_tsum_factoredNumbers_sub_tsum_lt
  statement: (hsum : Summable f) (hf₀ : f 0 = 0) {ε : Real}
  proof: by
  obtain ⟨N, hN⟩ :=
summable_iff_nat_tsum_vanishing.mp hsum (Metric.ball 0 ε) Metric.ball_mem_nhds 0 εpos
  simp_rw [mem_ball_zero_iff] at hN
  refine ⟨N, fun s hs => ?_⟩
have := hN _ factoredNumbers_compl hs
  rwa [← hsum.tsum_subtype_add_tsum_subtype_compl (factoredNumbers s),
    add_sub_cance

中文:
引理 norm_tsum_factoredNumbers_sub_tsum_lt
  结论: (hsum : Summable f) (hf₀ : f 0 = 0) {ε : 实数}
  证明: by
  obtain ⟨N, hN⟩ :=
summable_iff_nat_tsum_vanishing.mp hsum (Metric.ball 0 ε) Metric.ball_mem_nhds 0 εpos
  simp_rw [mem_ball_zero_iff] at hN
  refine ⟨N, fun s hs => ?_⟩
have := hN _ factoredNumbers_compl hs
  rwa [← hsum.tsum_subtype_add_tsum_subtype_compl (factoredNumbers s),
    add_sub_cance

Depends on / 依赖: Metric, Metric.ball, Metric.ball_mem_nhds, add_sub_cancel_left, ball_mem_nhds, factoredNumbers, factoredNumbers_compl, hsum.tsum_subtype_add_tsum_subtype_compl, mem_ball_zero_iff, simp_rw, summable_iff_nat_tsum_vanishing, summable_iff_nat_tsum_vanishing.mp, tsum_eq_tsum_sdiff_singleton, tsum_subtype_add_tsum_subtype_compl
-/
lemma norm_tsum_factoredNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0) {ε : Real}
    (εpos : 0 < ε) :
    exists N : Nat, forall s : Finset Nat, primesBelow N <= s ->
      ‖(∑' m : Nat, f m) - ∑' m : factoredNumbers s, f m‖ < ε := by
  obtain ⟨N, hN⟩ :=
summable_iff_nat_tsum_vanishing.mp hsum (Metric.ball 0 ε) Metric.ball_mem_nhds 0 εpos
  simp_rw [mem_ball_zero_iff] at hN
  refine ⟨N, fun s hs => ?_⟩
have := hN _ factoredNumbers_compl hs
  rwa [← hsum.tsum_subtype_add_tsum_subtype_compl (factoredNumbers s),
    add_sub_cancel_left, tsum_eq_tsum_sdiff_singleton (factoredNumbers s)ᶜ hf₀]

-- Versions of the three lemmas above for `smoothNumbers N`

include hf₁ hmul in
/--
lemma `summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum` / 引理 `summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`

English:
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
  proof: by
  rw [smoothNumbers_eq_factoredNumbers]; rw [primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul hsum _

include hf₁ hmul in

中文:
引理 summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
  证明: by
  rw [smoothNumbers_eq_factoredNumbers]; rw [primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul hsum _

include hf₁ hmul in

Depends on / 依赖: primesBelow, smoothNumbers_eq_factoredNumbers, summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
-/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (hsum : forall {p : Nat}, p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)) (N : Nat) :
    Summable (fun m : N.smoothNumbers => ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers => f m) (∏ p in N.primesBelow, ∑' n : Nat, f (p ^ n)) := by
  rw [smoothNumbers_eq_factoredNumbers]; rw [primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul hsum _

include hf₁ hmul in
/--
lemma `prod_primesBelow_tsum_eq_tsum_smoothNumbers` / 引理 `prod_primesBelow_tsum_eq_tsum_smoothNumbers`

English:
lemma prod_primesBelow_tsum_eq_tsum_smoothNumbers
  given: (hsum : Summable (‖f ·‖)) (N : Nat)
  proof: (summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
    (fun hp => hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

中文:
引理 prod_primesBelow_tsum_eq_tsum_smoothNumbers
  条件: (hsum : Summable (‖f ·‖)) (N : 自然数)
  证明: (summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
    (fun hp => hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

Depends on / 依赖: Nat.pow_right_injective, comp_injective, hp.one_lt, hsum.comp_injective, one_lt, pow_right_injective, summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum, tsum_eq, tsum_eq.symm
-/
lemma prod_primesBelow_tsum_eq_tsum_smoothNumbers (hsum : Summable (‖f ·‖)) (N : Nat) :
    ∏ p in N.primesBelow, ∑' n : Nat, f (p ^ n) = ∑' m : N.smoothNumbers, f m :=
  (summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
    (fun hp => hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

/--
lemma `norm_tsum_smoothNumbers_sub_tsum_lt` / 引理 `norm_tsum_smoothNumbers_sub_tsum_lt`

English:
lemma norm_tsum_smoothNumbers_sub_tsum_lt
  statement: (hsum : Summable f) (hf₀ : f 0 = 0)
  proof: by
  conv => enter [1, N₀, N]; rw [smoothNumbers_eq_factoredNumbers]
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum hf₀ εpos
  refine ⟨N₀, fun N hN => hN₀ (range N) fun p hp => ?_⟩
exact mem_range.mpr (lt_of_mem_primesBelow hp).trans_le hN


include hf₁ hmul in

中文:
引理 norm_tsum_smoothNumbers_sub_tsum_lt
  结论: (hsum : Summable f) (hf₀ : f 0 = 0)
  证明: by
  conv => enter [1, N₀, N]; rw [smoothNumbers_eq_factoredNumbers]
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum hf₀ εpos
  refine ⟨N₀, fun N hN => hN₀ (range N) fun p hp => ?_⟩
exact mem_range.mpr (lt_of_mem_primesBelow hp).trans_le hN


include hf₁ hmul in

Depends on / 依赖: SemilatticeSup, SupHomClass, SupHomClass.toOrderHomClass, lt_of_mem_primesBelow, mem_range, mem_range.mpr, norm_tsum_factoredNumbers_sub_tsum_lt, smoothNumbers_eq_factoredNumbers, toOrderHomClass, trans_le
-/
lemma norm_tsum_smoothNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0)
    {ε : Real} (εpos : 0 < ε) :
    exists N₀ : Nat, forall N >= N₀, ‖(∑' m : Nat, f m) - ∑' m : N.smoothNumbers, f m‖ < ε := by
  conv => enter [1, N₀, N]; rw [smoothNumbers_eq_factoredNumbers]
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum hf₀ εpos
  refine ⟨N₀, fun N hN => hN₀ (range N) fun p hp => ?_⟩
exact mem_range.mpr (lt_of_mem_primesBelow hp).trans_le hN


include hf₁ hmul in
/--
theorem `eulerProduct_hasProd` / 定理 `eulerProduct_hasProd`

English:
theorem eulerProduct_hasProd
  given: (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0)
  proof: by
  let F : Nat -> R := fun n => ∑' e, f (n ^ e)
  change HasProd (F ∘ Subtype.val (p := (· in {x | Nat.Prime x}))) _
  rw [hasProd_subtype_iff_mulIndicator]; rw [HasProd]; rw [SummationFilter.unconditional]; rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub

中文:
定理 eulerProduct_hasProd
  条件: (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0)
  证明: by
  let F : Nat -> R := fun n => ∑' e, f (n ^ e)
  change HasProd (F ∘ Subtype.val (p := (· in {x | Nat.Prime x}))) _
  rw [hasProd_subtype_iff_mulIndicator]; rw [HasProd]; rw [SummationFilter.unconditional]; rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub

Depends on / 依赖: HasProd, Metric, Metric.tendsto_atTop, Nat.Prime, OrderIsoClass, OrderIsoClass.toSupHomClass, SemilatticeSup, Subtype, Subtype.val, SummationFilter, SummationFilter.unconditional, hasProd_subtype_iff_mulIndicator, hsum.of_norm, mulIndicator, norm_tsum_factoredNumbers_sub_tsum_lt, of_norm, p.Prime, prod_mulIndicator_eq_prod_filter, tendsto_atTop, toSupHomClass
-/
theorem eulerProduct_hasProd (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    HasProd (fun p : Primes => ∑' e, f (p ^ e)) (∑' n, f n) := by
  let F : Nat -> R := fun n => ∑' e, f (n ^ e)
  change HasProd (F ∘ Subtype.val (p := (· in {x | Nat.Prime x}))) _
  rw [hasProd_subtype_iff_mulIndicator]; rw [HasProd]; rw [SummationFilter.unconditional]; rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum.of_norm hf₀ hε
  refine ⟨range N₀, fun s hs => ?_⟩
  have : ∏ p in s, {p | Nat.Prime p}.mulIndicator F p = ∏ p in s with p.Prime, F p :=
    prod_mulIndicator_eq_prod_filter s (fun _ => F) _ id
  rw [this]; rw [dist_eq_norm]; rw [prod_filter_prime_tsum_eq_tsum_factoredNumbers hf₁ hmul hsum]; rw [norm_sub_rev]
exact hN₀ s fun p hp => hs mem_range.mpr lt_of_mem_primesBelow hp

include hf₁ hmul in
/--
theorem `eulerProduct_hasProd_mulIndicator` / 定理 `eulerProduct_hasProd_mulIndicator`

English:
theorem eulerProduct_hasProd_mulIndicator
  given: (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0)
  proof: by
  rw [← hasProd_subtype_iff_mulIndicator]
  exact eulerProduct_hasProd hf₁ hmul hsum hf₀

中文:
定理 eulerProduct_hasProd_mulIndicator
  条件: (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0)
  证明: by
  rw [← hasProd_subtype_iff_mulIndicator]
  exact eulerProduct_hasProd hf₁ hmul hsum hf₀

Depends on / 依赖: Lattice, OrderIsoClass, OrderIsoClass.toLatticeHomClass, eulerProduct_hasProd, hasProd_subtype_iff_mulIndicator, toLatticeHomClass
-/
theorem eulerProduct_hasProd_mulIndicator (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    HasProd (Set.mulIndicator {p | Nat.Prime p} fun p => ∑' e, f (p ^ e)) (∑' n, f n) := by
  rw [← hasProd_subtype_iff_mulIndicator]
  exact eulerProduct_hasProd hf₁ hmul hsum hf₀

open Filter in
include hf₁ hmul in
/--
theorem `eulerProduct` / 定理 `eulerProduct`

English:
theorem eulerProduct
  given: (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0)
  proof: by
  have := (eulerProduct_hasProd_mulIndicator hf₁ hmul hsum hf₀).tendsto_prod_nat
  let F : Nat -> R := fun p => ∑' (e : Nat), f (p ^ e)
  have H (n : Nat) : ∏ i in range n, Set.mulIndicator {p | Nat.Prime p} F i =
                     ∏ p in primesBelow n, ∑' (e : Nat), f (p ^ e) :=
    prod_mulI

中文:
定理 eulerProduct
  条件: (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0)
  证明: by
  have := (eulerProduct_hasProd_mulIndicator hf₁ hmul hsum hf₀).tendsto_prod_nat
  let F : Nat -> R := fun p => ∑' (e : Nat), f (p ^ e)
  have H (n : Nat) : ∏ i in range n, Set.mulIndicator {p | Nat.Prime p} F i =
                     ∏ p in primesBelow n, ∑' (e : Nat), f (p ^ e) :=
    prod_mulI

Depends on / 依赖: Nat.Prime, Set.mulIndicator, eulerProduct_hasProd_mulIndicator, mulIndicator, primesBelow, prod_mulIndicator_eq_prod_filter, tendsto_prod_nat
-/
theorem eulerProduct (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    Tendsto (fun n : Nat => ∏ p in primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) := by
  have := (eulerProduct_hasProd_mulIndicator hf₁ hmul hsum hf₀).tendsto_prod_nat
  let F : Nat -> R := fun p => ∑' (e : Nat), f (p ^ e)
  have H (n : Nat) : ∏ i in range n, Set.mulIndicator {p | Nat.Prime p} F i =
                     ∏ p in primesBelow n, ∑' (e : Nat), f (p ^ e) :=
    prod_mulIndicator_eq_prod_filter (range n) (fun _ => F) (fun _ => {p | Nat.Prime p}) id
  simpa only [F, H]

include hf₁ hmul in
/--
theorem `eulerProduct_tprod` / 定理 `eulerProduct_tprod`

English:
theorem eulerProduct_tprod
  given: (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0)
  proof: (eulerProduct_hasProd hf₁ hmul hsum hf₀).tprod_eq

中文:
定理 eulerProduct_tprod
  条件: (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0)
  证明: (eulerProduct_hasProd hf₁ hmul hsum hf₀).tprod_eq

Depends on / 依赖: eulerProduct_hasProd, tprod_eq
-/
theorem eulerProduct_tprod (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    ∏' p : Primes, ∑' e, f (p ^ e) = ∑' n, f n :=
  (eulerProduct_hasProd hf₁ hmul hsum hf₀).tprod_eq

end EulerProduct

/-!
### Versions for arithmetic functions
-/

namespace ArithmeticFunction

open EulerProduct

/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`.
This version is stated in terms of `HasProd`. -/
nonrec theorem IsMultiplicative.eulerProduct_hasProd {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes => ∑' e, f (p ^ e)) (∑' n, f n) :=
  eulerProduct_hasProd hf.1 hf.2 hsum f.map_zero

open Filter in
/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`.
This version is stated in the form of convergence of finite partial products. -/
nonrec theorem IsMultiplicative.eulerProduct {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hsum : Summable (‖f ·‖)) :
    Tendsto (fun n : Nat => ∏ p in primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) :=
  eulerProduct hf.1 hf.2 hsum f.map_zero

/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`. -/
nonrec theorem IsMultiplicative.eulerProduct_tprod {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, ∑' e, f (p ^ e) = ∑' n, f n :=
  eulerProduct_tprod hf.1 hf.2 hsum f.map_zero

end ArithmeticFunction

end General

section CompletelyMultiplicative

/-!
### Euler Products for completely multiplicative functions

We now assume that `f` is completely multiplicative and has values in a complete normed field `F`.
Then we can use the formula for geometric series to simplify the statement. This leads to
`EulerProduct.eulerProduct_completely_multiplicative_hasProd` and variants.
-/

variable {F : Type*} [NormedField F] [CompleteSpace F]

namespace EulerProduct

-- a helper lemma that is useful below
/--
lemma `one_sub_inv_eq_geometric_of_summable_norm` / 引理 `one_sub_inv_eq_geometric_of_summable_norm`

English:
lemma one_sub_inv_eq_geometric_of_summable_norm
  statement: {f : Nat ->*₀ F} {p : Nat} (hp : p.Prime)
  proof: by
  simp only [map_pow]
  refine (tsum_geometric_of_norm_lt_one <| summable_geometric_iff_norm_lt_one.mp ?_).symm
  refine Summable.of_norm ?_
  simpa only [Function.comp_def, map_pow]
using hsum.comp_injective Nat.pow_right_injective hp.one_lt

中文:
引理 one_sub_inv_eq_geometric_of_summable_norm
  结论: {f : 自然数 ->*₀ F} {p : 自然数} (hp : p.Prime)
  证明: by
  simp only [map_pow]
  refine (tsum_geometric_of_norm_lt_one <| summable_geometric_iff_norm_lt_one.mp ?_).symm
  refine Summable.of_norm ?_
  simpa only [Function.comp_def, map_pow]
using hsum.comp_injective Nat.pow_right_injective hp.one_lt

Depends on / 依赖: Function, Function.comp_def, Nat.pow_right_injective, Summable, Summable.of_norm, comp_def, comp_injective, hp.one_lt, hsum.comp_injective, map_pow, of_norm, one_lt, pow_right_injective, summable_geometric_iff_norm_lt_one, summable_geometric_iff_norm_lt_one.mp, tsum_geometric_of_norm_lt_one
-/
lemma one_sub_inv_eq_geometric_of_summable_norm {f : Nat ->*₀ F} {p : Nat} (hp : p.Prime)
    (hsum : Summable fun x => ‖f x‖) :
    (1 - f p)⁻¹ = ∑' (e : Nat), f (p ^ e) := by
  simp only [map_pow]
  refine (tsum_geometric_of_norm_lt_one <| summable_geometric_iff_norm_lt_one.mp ?_).symm
  refine Summable.of_norm ?_
  simpa only [Function.comp_def, map_pow]
using hsum.comp_injective Nat.pow_right_injective hp.one_lt

/--
lemma `summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric` / 引理 `summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric`

English:
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
  statement: {f : Nat ->* F}
  proof: by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have H₁ :
      ∏ p in s with p.Prime, ∑' n : Nat, f (p ^ n) = ∏ p in s with p.Prime, (1 - f p)⁻¹ := by
    refine prod_congr rfl fun p hp => ?_
    simp only [map_pow]
exact tsum_geometric_of_norm_lt_one h (mem_filter.mp hp).2
  have H₂ 

中文:
引理 summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
  结论: {f : 自然数 ->* F}
  证明: by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have H₁ :
      ∏ p in s with p.Prime, ∑' n : Nat, f (p ^ n) = ∏ p in s with p.Prime, (1 - f p)⁻¹ := by
    refine prod_congr rfl fun p hp => ?_
    simp only [map_pow]
exact tsum_geometric_of_norm_lt_one h (mem_filter.mp hp).2
  have H₂ 

Depends on / 依赖: Coprime, Nat.Coprime, Summable, Summable.of_nonneg_of_le, f.map_mul, map_mul, map_pow, mem_filter, mem_filter.mp, norm_nonneg, norm_pow_le, of_nonneg_of_le, p.Prime, prod_congr, summable_geometric_iff_norm_lt, tsum_geometric_of_norm_lt_one
-/
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric {f : Nat ->* F}
    (h : forall {p : Nat}, p.Prime -> ‖f p‖ < 1) (s : Finset Nat) :
    Summable (fun m : factoredNumbers s => ‖f m‖) ∧
      HasSum (fun m : factoredNumbers s => f m) (∏ p in s with p.Prime, (1 - f p)⁻¹) := by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have H₁ :
      ∏ p in s with p.Prime, ∑' n : Nat, f (p ^ n) = ∏ p in s with p.Prime, (1 - f p)⁻¹ := by
    refine prod_congr rfl fun p hp => ?_
    simp only [map_pow]
exact tsum_geometric_of_norm_lt_one h (mem_filter.mp hp).2
  have H₂ : forall {p : Nat}, p.Prime -> Summable fun n => ‖f (p ^ n)‖ := by
    intro p hp
    simp only [map_pow]
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_pow_le ..) ?_
exact summable_geometric_iff_norm_lt_one.mpr (norm_norm (f p)).symm ▸ h hp
  exact H₁ ▸ summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum f.map_one hmul H₂ s

/--
lemma `prod_filter_prime_geometric_eq_tsum_factoredNumbers` / 引理 `prod_filter_prime_geometric_eq_tsum_factoredNumbers`

English:
lemma prod_filter_prime_geometric_eq_tsum_factoredNumbers
  statement: {f : Nat ->* F} (hsum : Summable f)
  proof: by
  refine (summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric ?_ s).2.tsum_eq.symm
  exact fun {_} hp => hsum.norm_lt_one hp.one_lt

中文:
引理 prod_filter_prime_geometric_eq_tsum_factoredNumbers
  结论: {f : 自然数 ->* F} (hsum : Summable f)
  证明: by
  refine (summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric ?_ s).2.tsum_eq.symm
  exact fun {_} hp => hsum.norm_lt_one hp.one_lt

Depends on / 依赖: hp.one_lt, hsum.norm_lt_one, norm_lt_one, one_lt, summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric, tsum_eq, tsum_eq.symm
-/
lemma prod_filter_prime_geometric_eq_tsum_factoredNumbers {f : Nat ->* F} (hsum : Summable f)
    (s : Finset Nat) :
    ∏ p in s with p.Prime, (1 - f p)⁻¹ = ∑' m : factoredNumbers s, f m := by
  refine (summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric ?_ s).2.tsum_eq.symm
  exact fun {_} hp => hsum.norm_lt_one hp.one_lt

/--
lemma `summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric` / 引理 `summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`

English:
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
  statement: {f : Nat ->* F}
  proof: by
  rw [smoothNumbers_eq_factoredNumbers]; rw [primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric h _

中文:
引理 summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
  结论: {f : 自然数 ->* F}
  证明: by
  rw [smoothNumbers_eq_factoredNumbers]; rw [primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric h _

Depends on / 依赖: primesBelow, smoothNumbers_eq_factoredNumbers, summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
-/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric {f : Nat ->* F}
    (h : forall {p : Nat}, p.Prime -> ‖f p‖ < 1) (N : Nat) :
    Summable (fun m : N.smoothNumbers => ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers => f m) (∏ p in N.primesBelow, (1 - f p)⁻¹) := by
  rw [smoothNumbers_eq_factoredNumbers]; rw [primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric h _

/--
lemma `prod_primesBelow_geometric_eq_tsum_smoothNumbers` / 引理 `prod_primesBelow_geometric_eq_tsum_smoothNumbers`

English:
lemma prod_primesBelow_geometric_eq_tsum_smoothNumbers
  given: {f : Nat ->* F} (hsum : Summable f) (N : Nat)
  proof: by
  rw [smoothNumbers_eq_factoredNumbers]; rw [primesBelow]
  exact prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum _

中文:
引理 prod_primesBelow_geometric_eq_tsum_smoothNumbers
  条件: {f : 自然数 ->* F} (hsum : Summable f) (N : 自然数)
  证明: by
  rw [smoothNumbers_eq_factoredNumbers]; rw [primesBelow]
  exact prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum _

Depends on / 依赖: primesBelow, prod_filter_prime_geometric_eq_tsum_factoredNumbers, smoothNumbers_eq_factoredNumbers
-/
lemma prod_primesBelow_geometric_eq_tsum_smoothNumbers {f : Nat ->* F} (hsum : Summable f) (N : Nat) :
    ∏ p in N.primesBelow, (1 - f p)⁻¹ = ∑' m : N.smoothNumbers, f m := by
  rw [smoothNumbers_eq_factoredNumbers]; rw [primesBelow]
  exact prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum _

/--
theorem `eulerProduct_completely_multiplicative_hasProd` / 定理 `eulerProduct_completely_multiplicative_hasProd`

English:
theorem eulerProduct_completely_multiplicative_hasProd
  given: {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖))
  proof: by
  have H : (fun p : Primes => (1 - f p)⁻¹) = fun p : Primes => ∑' (e : Nat), f (p ^ e) :=
funext fun p => one_sub_inv_eq_geometric_of_summable_norm p.prop hsum
  simpa only [map_pow, H]
    using eulerProduct_hasProd f.map_one (fun {m n} _ => f.map_mul m n) hsum f.map_zero

中文:
定理 eulerProduct_completely_multiplicative_hasProd
  条件: {f : 自然数 ->*₀ F} (hsum : Summable (‖f ·‖))
  证明: by
  have H : (fun p : Primes => (1 - f p)⁻¹) = fun p : Primes => ∑' (e : Nat), f (p ^ e) :=
funext fun p => one_sub_inv_eq_geometric_of_summable_norm p.prop hsum
  simpa only [map_pow, H]
    using eulerProduct_hasProd f.map_one (fun {m n} _ => f.map_mul m n) hsum f.map_zero

Depends on / 依赖: Primes, eulerProduct_hasProd, f.map_mul, f.map_one, f.map_zero, map_mul, map_one, map_pow, map_zero, one_sub_inv_eq_geometric_of_summable_norm, p.prop
-/
theorem eulerProduct_completely_multiplicative_hasProd {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes => (1 - f p)⁻¹) (∑' n, f n) := by
  have H : (fun p : Primes => (1 - f p)⁻¹) = fun p : Primes => ∑' (e : Nat), f (p ^ e) :=
funext fun p => one_sub_inv_eq_geometric_of_summable_norm p.prop hsum
  simpa only [map_pow, H]
    using eulerProduct_hasProd f.map_one (fun {m n} _ => f.map_mul m n) hsum f.map_zero

/--
theorem `eulerProduct_completely_multiplicative_tprod` / 定理 `eulerProduct_completely_multiplicative_tprod`

English:
theorem eulerProduct_completely_multiplicative_tprod
  given: {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖))
  proof: (eulerProduct_completely_multiplicative_hasProd hsum).tprod_eq

中文:
定理 eulerProduct_completely_multiplicative_tprod
  条件: {f : 自然数 ->*₀ F} (hsum : Summable (‖f ·‖))
  证明: (eulerProduct_completely_multiplicative_hasProd hsum).tprod_eq

Depends on / 依赖: eulerProduct_completely_multiplicative_hasProd, tprod_eq
-/
theorem eulerProduct_completely_multiplicative_tprod {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, (1 - f p)⁻¹ = ∑' n, f n :=
  (eulerProduct_completely_multiplicative_hasProd hsum).tprod_eq

open Filter in
/--
theorem `eulerProduct_completely_multiplicative` / 定理 `eulerProduct_completely_multiplicative`

English:
theorem eulerProduct_completely_multiplicative
  given: {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖))
  proof: by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have := (eulerProduct_hasProd_mulIndicator f.map_one hmul hsum f.map_zero).tendsto_prod_nat
  have H (n : Nat) : ∏ p in range n, {p | Nat.Prime p}.mulIndicator (fun p => (1 - f p)⁻¹) p =
                     ∏ p in primesBelow n, (1 - f p

中文:
定理 eulerProduct_completely_multiplicative
  条件: {f : 自然数 ->*₀ F} (hsum : Summable (‖f ·‖))
  证明: by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have := (eulerProduct_hasProd_mulIndicator f.map_one hmul hsum f.map_zero).tendsto_prod_nat
  have H (n : Nat) : ∏ p in range n, {p | Nat.Prime p}.mulIndicator (fun p => (1 - f p)⁻¹) p =
                     ∏ p in primesBelow n, (1 - f p

Depends on / 依赖: Coprime, Nat.Coprime, Nat.Prime, eulerProduct_hasProd_mulIndicator, f.map_mul, f.map_one, f.map_zero, map_mul, map_one, map_zero, mulIndicator, primesBelow, prod_mulIndicator_eq_prod_filter, tendsto_prod_nat
-/
theorem eulerProduct_completely_multiplicative {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖)) :
    Tendsto (fun n : Nat => ∏ p in primesBelow n, (1 - f p)⁻¹) atTop (𝓝 (∑' n, f n)) := by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have := (eulerProduct_hasProd_mulIndicator f.map_one hmul hsum f.map_zero).tendsto_prod_nat
  have H (n : Nat) : ∏ p in range n, {p | Nat.Prime p}.mulIndicator (fun p => (1 - f p)⁻¹) p =
                     ∏ p in primesBelow n, (1 - f p)⁻¹ :=
    prod_mulIndicator_eq_prod_filter
      (range n) (fun _ p => (1 - f p)⁻¹) (fun _ => {p | Nat.Prime p}) id
  have H' : {p | Nat.Prime p}.mulIndicator (fun p => (1 - f p)⁻¹) =
              {p | Nat.Prime p}.mulIndicator (fun p => ∑' e : Nat, f (p ^ e)) :=
    Set.mulIndicator_congr fun p hp => one_sub_inv_eq_geometric_of_summable_norm hp hsum
  simpa only [← H, H'] using this

end EulerProduct

end CompletelyMultiplicative

section PrimePow

/-! ### Reindexing infinite sums and products over prime powers -/

open Nat.Primes

variable {α : Type*} [CommGroup α] [UniformSpace α] [IsUniformGroup α] [CompleteSpace α] [T0Space α]
variable {f : Nat -> α}

@[to_additive tsum_primes_pow_eq]
/--
theorem `tprod_primes_pow_eq` / 定理 `tprod_primes_pow_eq`

English:
theorem tprod_primes_pow_eq
  given: (hf : Multipliable fun n : {n // IsPrimePow n} => f n.1)
  proof: calc
  _ = ∏' p : Nat.Primes × Nat, f (prodNatEquiv p) := by
    simpa using (hf.comp_injective prodNatEquiv.injective).tprod_prod.symm
  _ = _ := by rw [← Equiv.tprod_eq prodNatEquiv]

@[to_additive tsum_eq_tsum_primes_of_support_subset_prime_powers]

中文:
定理 tprod_primes_pow_eq
  条件: (hf : Multipliable fun n : {n // IsPrimePow n} => f n.1)
  证明: calc
  _ = ∏' p : Nat.Primes × Nat, f (prodNatEquiv p) := by
    simpa using (hf.comp_injective prodNatEquiv.injective).tprod_prod.symm
  _ = _ := by rw [← Equiv.tprod_eq prodNatEquiv]

@[to_additive tsum_eq_tsum_primes_of_support_subset_prime_powers]
-/
theorem tprod_primes_pow_eq (hf : Multipliable fun n : {n // IsPrimePow n} => f n.1) :
    ∏' (p : Nat.Primes) (n : Nat), f (p ^ (n + 1)) = ∏' n : {n : Nat // IsPrimePow n}, f n := calc
  _ = ∏' p : Nat.Primes × Nat, f (prodNatEquiv p) := by
    simpa using (hf.comp_injective prodNatEquiv.injective).tprod_prod.symm
  _ = _ := by rw [← Equiv.tprod_eq prodNatEquiv]

@[to_additive tsum_eq_tsum_primes_of_support_subset_prime_powers]
/--
lemma `tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers` / 引理 `tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers`

English:
lemma tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers
  proof: by
  rw [tprod_primes_pow_eq (hfm.subtype _)]
  exact (tprod_subtype_eq_of_mulSupport_subset hf).symm

@[to_additive tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers]

中文:
引理 tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers
  证明: by
  rw [tprod_primes_pow_eq (hfm.subtype _)]
  exact (tprod_subtype_eq_of_mulSupport_subset hf).symm

@[to_additive tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers]

Depends on / 依赖: hfm.subtype, subtype, tprod_primes_pow_eq, tprod_subtype_eq_of_mulSupport_subset
-/
lemma tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers
    (hfm : Multipliable f) (hf : Function.mulSupport f subseteq {n | IsPrimePow n}) :
    ∏' n : Nat, f n = ∏' (p : Nat.Primes) (k : Nat), f (p ^ (k + 1)) := by
  rw [tprod_primes_pow_eq (hfm.subtype _)]
  exact (tprod_subtype_eq_of_mulSupport_subset hf).symm

@[to_additive tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers]
/--
lemma `tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers` / 引理 `tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers`

English:
lemma tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers
  proof: by
  rw [tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers hfm hf]
  have hfs' (p : Nat.Primes) : Multipliable fun k => f (p ^ (k + 1)) :=
hfm.comp_injective (strictMono_nat_of_lt_succ
      (pow_lt_pow_right₀ p.prop.one_lt <| lt_add_one <| · + 1)).injective
  simp only [(hfs' _).tprod_eq_zero

中文:
引理 tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers
  证明: by
  rw [tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers hfm hf]
  have hfs' (p : Nat.Primes) : Multipliable fun k => f (p ^ (k + 1)) :=
hfm.comp_injective (strictMono_nat_of_lt_succ
      (pow_lt_pow_right₀ p.prop.one_lt <| lt_add_one <| · + 1)).injective
  simp only [(hfs' _).tprod_eq_zero

Depends on / 依赖: Multipliable, Multipliable.subtype, Nat.Primes, Primes, Subtype, Subtype.val_injective.comp, comp_injective, hfm.comp_injective, injective, lt_add_one, one_lt, p.prop.one_lt, pow_one, prodNat, strictMono_nat_of_lt_succ, subtype, tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers, tprod_eq_zero_mul, tprod_mul, val_injective
-/
lemma tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers
    (hfm : Multipliable f) (hf : Function.mulSupport f subseteq {n | IsPrimePow n}) :
    ∏' n : Nat, f n = (∏' p : Nat.Primes, f p) * ∏' (p : Nat.Primes) (k : Nat), f (p ^ (k + 2)) := by
  rw [tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers hfm hf]
  have hfs' (p : Nat.Primes) : Multipliable fun k => f (p ^ (k + 1)) :=
hfm.comp_injective (strictMono_nat_of_lt_succ
      (pow_lt_pow_right₀ p.prop.one_lt <| lt_add_one <| · + 1)).injective
  simp only [(hfs' _).tprod_eq_zero_mul, zero_add, pow_one]
  apply (Multipliable.subtype hfm _).tprod_mul
  refine (hfm.comp_injective ?_).prod (f := fun (pk : Nat.Primes × Nat) => f (pk.1 ^ (pk.2 + 2)))
.comp exact Subtype.val_injective.comp prodNatEquiv.injective
Function.Injective.prodMap (fun ⦃_ _⦄ => id) add_left_injective 1

end PrimePow
