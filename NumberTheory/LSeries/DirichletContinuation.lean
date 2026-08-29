/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Michael Stoll
-/
module

public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Analytic continuation of Dirichlet L-functions

We show that if `χ` is a Dirichlet character `ZMod N → ℂ`, for a positive integer `N`, then the
L-series of `χ` has analytic continuation (away from a pole at `s = 1` if `χ` is trivial), and
similarly for completed L-functions.

All definitions and theorems are in the `DirichletCharacter` namespace.

## Main definitions

* `LFunction χ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.
* `completedLFunction χ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction χ s * gammaFactor χ s` where `gammaFactor χ s` is the archimedean Gamma-factor.
* `rootNumber`: the global root number of the L-series of `χ` (for `χ` primitive; junk otherwise).

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `differentiable_LFunction`: if `χ` is nontrivial then `LFunction χ s` is differentiable
  everywhere.
* `LFunction_eq_completed_div_gammaFactor`: we have
  `LFunction χ s = completedLFunction χ s / gammaFactor χ s`, unless `s = 0` and `χ` is the trivial
  character modulo 1.
* `differentiable_completedLFunction`: if `χ` is nontrivial then `completedLFunction χ s` is
  differentiable everywhere.
* `IsPrimitive.completedLFunction_one_sub`: the **functional equation** for Dirichlet L-functions,
  showing that if `χ` is primitive modulo `N`, then
  `completedLFunction χ s = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s`.
-/

@[expose] public section

open HurwitzZeta Complex Finset ZMod Filter

open scoped Real Topology

namespace DirichletCharacter

variable {N : Nat} [NeZero N]

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, χ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries χ`: they agree in the convergence range, but
`LSeries χ s` is defined to be `0` if `re s ≤ 1`.
-/
@[pp_nodot]
/--
Definition of `LFunction` / `LFunction` 的定义

English:
definition LFunction
  signature: (χ : DirichletCharacter Complex N) (s : Complex)
  body: ZMod.LFunction χ s

中文:
定义 L函数
  签名: (χ : DirichletCharacter 复形 N) (s : 复形)
  定义体: ZMod.LFunction χ s

Depends on / 依赖: LFunction, ZMod.LFunction
-/
noncomputable def LFunction (χ : DirichletCharacter Complex N) (s : Complex) : Complex := ZMod.LFunction χ s

/--
lemma `LFunction_modOne_eq` / 引理 `LFunction_modOne_eq`

English:
lemma LFunction_modOne_eq
  given: {χ : DirichletCharacter Complex 1}
  proof: by
  ext; rw [LFunction, ZMod.LFunction_modOne_eq, (by rfl : (0 : ZMod 1) = 1), map_one, one_mul]

中文:
引理 LFunction_modOne_eq
  条件: {χ : DirichletCharacter 复形 1}
  证明: by
  ext; rw [LFunction, ZMod.LFunction_modOne_eq, (by rfl : (0 : ZMod 1) = 1), map_one, one_mul]
-/
@[simp] lemma LFunction_modOne_eq {χ : DirichletCharacter Complex 1} :
    LFunction χ = riemannZeta := by
  ext; rw [LFunction, ZMod.LFunction_modOne_eq, (by rfl : (0 : ZMod 1) = 1), map_one, one_mul]

/--
lemma `LFunction_eq_LSeries` / 引理 `LFunction_eq_LSeries`

English:
lemma LFunction_eq_LSeries
  given: (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < re s)
  proof: ZMod.LFunction_eq_LSeries χ hs

中文:
引理 LFunction_eq_LSeries
  条件: (χ : DirichletCharacter 复形 N) {s : 复形} (hs : 1 < re s)
  证明: ZMod.LFunction_eq_LSeries χ hs

Depends on / 依赖: LFunction_eq_LSeries, ZMod.LFunction_eq_LSeries
-/
lemma LFunction_eq_LSeries (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < re s) :
    LFunction χ s = LSeries (χ ·) s :=
  ZMod.LFunction_eq_LSeries χ hs

/--
lemma `deriv_LFunction_eq_deriv_LSeries` / 引理 `deriv_LFunction_eq_deriv_LSeries`

English:
lemma deriv_LFunction_eq_deriv_LSeries
  given: (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
  proof: by
  refine Filter.EventuallyEq.deriv_eq ?_
  have h : {z | 1 < z.re} in nhds s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [h] with z hz
  exact LFunction_eq_LSeries χ hz

中文:
引理 deriv_LFunction_eq_deriv_LSeries
  条件: (χ : DirichletCharacter 复形 N) {s : 复形} (hs : 1 < s.re)
  证明: by
  refine Filter.EventuallyEq.deriv_eq ?_
  have h : {z | 1 < z.re} in nhds s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [h] with z hz
  exact LFunction_eq_LSeries χ hz

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.deriv_eq, LFunction_eq_LSeries, continuous_const, continuous_re, deriv_eq, filter_upwards, isOpen_lt, mem_nhds, z.re
-/
lemma deriv_LFunction_eq_deriv_LSeries (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re) :
    deriv (LFunction χ) s = deriv (LSeries (χ ·)) s := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have h : {z | 1 < z.re} in nhds s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [h] with z hz
  exact LFunction_eq_LSeries χ hz

/--
The L-function of a Dirichlet character is differentiable, except at `s = 1` if the character is
trivial.
-/
@[fun_prop]
/--
lemma `differentiableAt_LFunction` / 引理 `differentiableAt_LFunction`

English:
lemma differentiableAt_LFunction
  given: (χ : DirichletCharacter Complex N) (s : Complex) (hs : s != 1 ∨ χ != 1)
  proof: ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)

中文:
引理 differentiableAt_LFunction
  条件: (χ : DirichletCharacter 复形 N) (s : 复形) (hs : s != 1 ∨ χ != 1)
  证明: ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)

Depends on / 依赖: ZMod.differentiableAt_LFunction, differentiableAt_LFunction, hs.imp_right, imp_right, sum_eq_zero_of_ne_one
-/
lemma differentiableAt_LFunction (χ : DirichletCharacter Complex N) (s : Complex) (hs : s != 1 ∨ χ != 1) :
    DifferentiableAt Complex (LFunction χ) s :=
  ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)

/-- The L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
@[fun_prop]
/--
lemma `differentiable_LFunction` / 引理 `differentiable_LFunction`

English:
lemma differentiable_LFunction
  given: {χ : DirichletCharacter Complex N} (hχ : χ != 1)
  proof: (differentiableAt_LFunction _ · <| Or.inr hχ)

中文:
引理 differentiable_LFunction
  条件: {χ : DirichletCharacter 复形 N} (hχ : χ != 1)
  证明: (differentiableAt_LFunction _ · <| Or.inr hχ)

Depends on / 依赖: Or.inr, differentiableAt_LFunction
-/
lemma differentiable_LFunction {χ : DirichletCharacter Complex N} (hχ : χ != 1) :
    Differentiable Complex (LFunction χ) :=
  (differentiableAt_LFunction _ · <| Or.inr hχ)

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
@[simp]
/--
lemma `Even.LFunction_neg_two_mul_nat_add_one` / 引理 `Even.LFunction_neg_two_mul_nat_add_one`

English:
lemma Even.LFunction_neg_two_mul_nat_add_one
  given: {χ : DirichletCharacter Complex N} (hχ : Even χ) (n : Nat)
  proof: ZMod.LFunction_neg_two_mul_nat_add_one hχ.to_fun n

中文:
引理 Even.LFunction_neg_two_mul_nat_add_one
  条件: {χ : DirichletCharacter 复形 N} (hχ : Even χ) (n : 自然数)
  证明: ZMod.LFunction_neg_two_mul_nat_add_one hχ.to_fun n

Depends on / 依赖: LFunction_neg_two_mul_nat_add_one, ZMod.LFunction_neg_two_mul_nat_add_one, to_fun
-/
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter Complex N} (hχ : Even χ) (n : Nat) :
    LFunction χ (-(2 * (n + 1))) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_add_one hχ.to_fun n

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
@[simp]
/--
lemma `Even.LFunction_neg_two_mul_nat` / 引理 `Even.LFunction_neg_two_mul_nat`

English:
lemma Even.LFunction_neg_two_mul_nat
  given: {χ : DirichletCharacter Complex N} (hχ : Even χ) (n : Nat) [NeZero n]
  proof: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact_mod_cast hχ.LFunction_neg_two_mul_nat_add_one m

中文:
引理 Even.LFunction_neg_two_mul_nat
  条件: {χ : DirichletCharacter 复形 N} (hχ : Even χ) (n : 自然数) [NeZero n]
  证明: by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact_mod_cast hχ.LFunction_neg_two_mul_nat_add_one m

Depends on / 依赖: LFunction_neg_two_mul_nat_add_one, Nat.exists_eq_succ_of_ne_zero, NeZero, NeZero.ne, exists_eq_succ_of_ne_zero
-/
lemma Even.LFunction_neg_two_mul_nat {χ : DirichletCharacter Complex N} (hχ : Even χ) (n : Nat) [NeZero n] :
    LFunction χ (-(2 * n)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact_mod_cast hχ.LFunction_neg_two_mul_nat_add_one m

/--
lemma `Odd.LFunction_neg_two_mul_nat_sub_one` / 引理 `Odd.LFunction_neg_two_mul_nat_sub_one`

English:
lemma Odd.LFunction_neg_two_mul_nat_sub_one
  proof: ZMod.LFunction_neg_two_mul_nat_sub_one hχ.to_fun n

中文:
引理 Odd.LFunction_neg_two_mul_nat_sub_one
  证明: ZMod.LFunction_neg_two_mul_nat_sub_one hχ.to_fun n
-/
@[simp] lemma Odd.LFunction_neg_two_mul_nat_sub_one
    {χ : DirichletCharacter Complex N} (hχ : Odd χ) (n : Nat) :
    LFunction χ (-(2 * n) - 1) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_sub_one hχ.to_fun n


/--
lemma `LFunction_changeLevel_aux` / 引理 `LFunction_changeLevel_aux`

English:
lemma LFunction_changeLevel_aux
  statement: {M N : Nat} [NeZero M] [NeZero N] (hMN : M ∣ N)
  proof: by
  have hpc : IsPreconnected ({1}ᶜ : Set Complex) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _)
.isPreconnected
  have hne : 2 in ({1}ᶜ : Set Complex) := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := Complex)
    (g := fun s => LFunction χ s * ∏ p in N.primeFactors, (1 - χ p * p ^ (-s))) ?_ ?_ hpc hne ?_ hs
  · refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_compl_singleton
    exact (differentiableAt_LFunction _ _ (.inl hs)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_compl_singleton
    refine ((differentiableAt_LFunction _ _ (.inl hs)).mul ?_).differentiableWithinAt
    refine .fun_finsetProd fun i h => ?_
    have : NeZero i := ⟨(Nat.pos_of_mem_primeFactors h).ne'⟩
    fun_prop
  · refine eventually_of_mem ?_ (fun t (ht : 1 < t.re) => ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : Complex).re)
    · simpa [LFunction_eq_LSeries _ ht] using LSeries_changeLevel hMN χ ht

中文:
引理 LFunction_changeLevel_aux
  结论: {M N : 自然数} [NeZero M] [NeZero N] (hMN : M ∣ N)
  证明: by
  have hpc : IsPreconnected ({1}ᶜ : Set Complex) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _)
.isPreconnected
  have hne : 2 in ({1}ᶜ : Set Complex) := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := Complex)
    (g := fun s => LFunction χ s * ∏ p in N.primeFactors, (1 - χ p * p ^ (-s))) ?_ ?_ hpc hne ?_ hs
  · refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_compl_singleton
    exact (differentiableAt_LFunction _ _ (.inl hs)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_compl_singleton
    refine ((differentiableAt_LFunction _ _ (.inl hs)).mul ?_).differentiableWithinAt
    refine .fun_finsetProd fun i h => ?_
    have : NeZero i := ⟨(Nat.pos_of_mem_primeFactors h).ne'⟩
    fun_prop
  · refine eventually_of_mem ?_ (fun t (ht : 1 < t.re) => ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : Complex).re)
    · simpa [LFunction_eq_LSeries _ ht] using LSeries_changeLevel hMN χ ht
-/
private lemma LFunction_changeLevel_aux {M N : Nat} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter Complex M) {s : Complex} (hs : s != 1) :
    LFunction (changeLevel hMN χ) s =
      LFunction χ s * ∏ p in N.primeFactors, (1 - χ p * p ^ (-s)) := by
  have hpc : IsPreconnected ({1}ᶜ : Set Complex) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _)
.isPreconnected
  have hne : 2 in ({1}ᶜ : Set Complex) := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := Complex)
    (g := fun s => LFunction χ s * ∏ p in N.primeFactors, (1 - χ p * p ^ (-s))) ?_ ?_ hpc hne ?_ hs
  · refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_compl_singleton
    exact (differentiableAt_LFunction _ _ (.inl hs)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_compl_singleton
    refine ((differentiableAt_LFunction _ _ (.inl hs)).mul ?_).differentiableWithinAt
    refine .fun_finsetProd fun i h => ?_
    have : NeZero i := ⟨(Nat.pos_of_mem_primeFactors h).ne'⟩
    fun_prop
  · refine eventually_of_mem ?_ (fun t (ht : 1 < t.re) => ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : Complex).re)
    · simpa [LFunction_eq_LSeries _ ht] using LSeries_changeLevel hMN χ ht

/--
lemma `LFunction_changeLevel` / 引理 `LFunction_changeLevel`

English:
lemma LFunction_changeLevel
  statement: {M N : Nat} [NeZero M] [NeZero N] (hMN : M ∣ N)
  proof: by
  rcases h with h | h
  · have hχ : changeLevel hMN χ != 1 := h ∘ (changeLevel_eq_one_iff hMN).mp
    have h' : Continuous fun s => LFunction χ s * ∏ p in N.primeFactors, (1 - χ p * ↑p ^ (-s)) :=
(differentiable_LFunction h).continuous.mul continuous_finsetProd _ fun p hp => by
        have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
        fun_prop
    exact congrFun ((differentiable_LFunction hχ).continuous.ext_on
      (dense_compl_singleton 1) h' (fun _ h => LFunction_changeLevel_aux hMN χ h)) s
  · exact LFunction_changeLevel_aux hMN χ h

中文:
引理 LFunction_changeLevel
  结论: {M N : 自然数} [NeZero M] [NeZero N] (hMN : M ∣ N)
  证明: by
  rcases h with h | h
  · have hχ : changeLevel hMN χ != 1 := h ∘ (changeLevel_eq_one_iff hMN).mp
    have h' : Continuous fun s => LFunction χ s * ∏ p in N.primeFactors, (1 - χ p * ↑p ^ (-s)) :=
(differentiable_LFunction h).continuous.mul continuous_finsetProd _ fun p hp => by
        have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
        fun_prop
    exact congrFun ((differentiable_LFunction hχ).continuous.ext_on
      (dense_compl_singleton 1) h' (fun _ h => LFunction_changeLevel_aux hMN χ h)) s
  · exact LFunction_changeLevel_aux hMN χ h

Depends on / 依赖: Continuous, LFunction, LFunction_changeLevel_aux, N.primeFactors, Nat.prime_of_mem_primeFactors, NeZero, changeLevel, changeLevel_eq_one_iff, continuous, continuous.ext_on, continuous.mul, continuous_finsetProd, dense_compl_singleton, differentiable_LFunction, ext_on, fun_prop, ne_zero, primeFactors, prime_of_mem_primeFactors
-/
lemma LFunction_changeLevel {M N : Nat} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter Complex M) {s : Complex} (h : χ != 1 ∨ s != 1) :
    LFunction (changeLevel hMN χ) s =
      LFunction χ s * ∏ p in N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rcases h with h | h
  · have hχ : changeLevel hMN χ != 1 := h ∘ (changeLevel_eq_one_iff hMN).mp
    have h' : Continuous fun s => LFunction χ s * ∏ p in N.primeFactors, (1 - χ p * ↑p ^ (-s)) :=
(differentiable_LFunction h).continuous.mul continuous_finsetProd _ fun p hp => by
        have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
        fun_prop
    exact congrFun ((differentiable_LFunction hχ).continuous.ext_on
      (dense_compl_singleton 1) h' (fun _ h => LFunction_changeLevel_aux hMN χ h)) s
  · exact LFunction_changeLevel_aux hMN χ h

/-!
### The `L`-function of the trivial character mod `N`
-/

/--
Definition of `LFunctionTrivChar` / `LFunctionTrivChar` 的定义

English:
abbreviation LFunctionTrivChar
  signature: (N : Nat) [NeZero N]
  body: (1 : DirichletCharacter Complex N).LFunction

中文:
缩写 LFunctionTrivChar
  签名: (N : 自然数) [NeZero N]
  定义体: (1 : DirichletCharacter Complex N).LFunction

Depends on / 依赖: DirichletCharacter, LFunction
-/
noncomputable abbrev LFunctionTrivChar (N : Nat) [NeZero N] :=
  (1 : DirichletCharacter Complex N).LFunction

/--
lemma `LFunctionTrivChar_eq_mul_riemannZeta` / 引理 `LFunctionTrivChar_eq_mul_riemannZeta`

English:
lemma LFunctionTrivChar_eq_mul_riemannZeta
  given: {s : Complex} (hs : s != 1)
  proof: by
  rw [← LFunction_modOne_eq (χ := 1)]; rw [LFunctionTrivChar]; rw [← changeLevel_one N.one_dvd]; rw [mul_comm]
  convert! LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _]; rw [one_mul]

中文:
引理 LFunctionTrivChar_eq_mul_riemannZeta
  条件: {s : 复形} (hs : s != 1)
  证明: by
  rw [← LFunction_modOne_eq (χ := 1)]; rw [LFunctionTrivChar]; rw [← changeLevel_one N.one_dvd]; rw [mul_comm]
  convert! LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _]; rw [one_mul]

Depends on / 依赖: LFunctionTrivChar, LFunction_changeLevel, LFunction_modOne_eq, MulChar, MulChar.one_apply, N.one_dvd, changeLevel_one, convert, isUnit_of_subsingleton, mul_comm, one_apply, one_dvd, one_mul
-/
lemma LFunctionTrivChar_eq_mul_riemannZeta {s : Complex} (hs : s != 1) :
    LFunctionTrivChar N s = (∏ p in N.primeFactors, (1 - (p : Complex) ^ (-s))) * riemannZeta s := by
  rw [← LFunction_modOne_eq (χ := 1)]; rw [LFunctionTrivChar]; rw [← changeLevel_one N.one_dvd]; rw [mul_comm]
  convert! LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _]; rw [one_mul]

/--
lemma `LFunctionTrivChar_residue_one` / 引理 `LFunctionTrivChar_residue_one`

English:
lemma LFunctionTrivChar_residue_one
  proof: by
  have H : (fun s => (s - 1) * LFunctionTrivChar N s) =ᶠ[𝓝[!=] 1]
        fun s => (∏ p in N.primeFactors, (1 - (p : Complex) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs => ?_
    rw [mul_left_comm]; rw [LFunctionTrivChar_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  refine .mul (f := fun s => ∏ p in N.primeFactors, _) ?_ riemannZeta_residue_one
refine tendsto_nhdsWithin_of_tendsto_nhds Continuous.tendsto ?_ 1
  exact continuous_finsetProd _ fun p hp => by
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop

中文:
引理 LFunctionTrivChar_residue_one
  证明: by
  have H : (fun s => (s - 1) * LFunctionTrivChar N s) =ᶠ[𝓝[!=] 1]
        fun s => (∏ p in N.primeFactors, (1 - (p : Complex) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs => ?_
    rw [mul_left_comm]; rw [LFunctionTrivChar_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  refine .mul (f := fun s => ∏ p in N.primeFactors, _) ?_ riemannZeta_residue_one
refine tendsto_nhdsWithin_of_tendsto_nhds Continuous.tendsto ?_ 1
  exact continuous_finsetProd _ fun p hp => by
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop

Depends on / 依赖: Finset, Finset.prod, LFunctionTrivChar, LFunctionTrivChar_eq_mul_riemannZeta, N.primeFactors, Set.EqOn.eventuallyEq_nhdsWithin, cpow_neg_one, eventuallyEq_nhdsWithin, mul_left_comm, mul_one, primeFactors, riemannZeta, riemannZeta_residue_one, tendsto_congr, tendsto_nhdsWith
-/
lemma LFunctionTrivChar_residue_one :
    Tendsto (fun s => (s - 1) * LFunctionTrivChar N s) (𝓝[!=] 1)
      (𝓝 <| ∏ p in N.primeFactors, (1 - (p : Complex)⁻¹)) := by
  have H : (fun s => (s - 1) * LFunctionTrivChar N s) =ᶠ[𝓝[!=] 1]
        fun s => (∏ p in N.primeFactors, (1 - (p : Complex) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs => ?_
    rw [mul_left_comm]; rw [LFunctionTrivChar_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  refine .mul (f := fun s => ∏ p in N.primeFactors, _) ?_ riemannZeta_residue_one
refine tendsto_nhdsWithin_of_tendsto_nhds Continuous.tendsto ?_ 1
  exact continuous_finsetProd _ fun p hp => by
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop

/-!
### Completed L-functions and the functional equation
-/

section gammaFactor

omit [NeZero N] -- not required for these declarations

open scoped Classical in
/--
Definition of `gammaFactor` / `gammaFactor` 的定义

English:
definition gammaFactor
  signature: (χ : DirichletCharacter Complex N) (s : Complex)
  body: if χ.Even then GammaReal s else GammaReal (s + 1)

中文:
定义 gammaFactor
  签名: (χ : DirichletCharacter 复形 N) (s : 复形)
  定义体: if χ.Even then GammaReal s else GammaReal (s + 1)

Depends on / 依赖: GammaReal
-/
noncomputable def gammaFactor (χ : DirichletCharacter Complex N) (s : Complex) :=
  if χ.Even then GammaReal s else GammaReal (s + 1)

/--
lemma `Even.gammaFactor_def` / 引理 `Even.gammaFactor_def`

English:
lemma Even.gammaFactor_def
  given: {χ : DirichletCharacter Complex N} (hχ : χ.Even) (s : Complex)
  proof: by
  simp [gammaFactor, hχ]

中文:
引理 Even.gammaFactor_def
  条件: {χ : DirichletCharacter 复形 N} (hχ : χ.Even) (s : 复形)
  证明: by
  simp [gammaFactor, hχ]

Depends on / 依赖: gammaFactor
-/
lemma Even.gammaFactor_def {χ : DirichletCharacter Complex N} (hχ : χ.Even) (s : Complex) :
    gammaFactor χ s = GammaReal s := by
  simp [gammaFactor, hχ]

/--
lemma `Odd.gammaFactor_def` / 引理 `Odd.gammaFactor_def`

English:
lemma Odd.gammaFactor_def
  given: {χ : DirichletCharacter Complex N} (hχ : χ.Odd) (s : Complex)
  proof: by
  simp [gammaFactor, hχ.not_even]

中文:
引理 Odd.gammaFactor_def
  条件: {χ : DirichletCharacter 复形 N} (hχ : χ.Odd) (s : 复形)
  证明: by
  simp [gammaFactor, hχ.not_even]

Depends on / 依赖: gammaFactor, not_even
-/
lemma Odd.gammaFactor_def {χ : DirichletCharacter Complex N} (hχ : χ.Odd) (s : Complex) :
    gammaFactor χ s = GammaReal (s + 1) := by
  simp [gammaFactor, hχ.not_even]

end gammaFactor

/--
Definition of `completedLFunction` / `completedLFunction` 的定义

English:
definition completedLFunction
  signature: (χ : DirichletCharacter Complex N) (s : Complex)
  body: ZMod.completedLFunction χ s

中文:
定义 completedLFunction
  签名: (χ : DirichletCharacter 复形 N) (s : 复形)
  定义体: ZMod.completedLFunction χ s
-/
@[pp_nodot] noncomputable def completedLFunction (χ : DirichletCharacter Complex N) (s : Complex) : Complex :=
  ZMod.completedLFunction χ s

/--
lemma `completedLFunction_modOne_eq` / 引理 `completedLFunction_modOne_eq`

English:
lemma completedLFunction_modOne_eq
  given: {χ : DirichletCharacter Complex 1}
  proof: by
  ext; rw [completedLFunction, ZMod.completedLFunction_modOne_eq, map_one, one_mul]

中文:
引理 completedLFunction_modOne_eq
  条件: {χ : DirichletCharacter 复形 1}
  证明: by
  ext; rw [completedLFunction, ZMod.completedLFunction_modOne_eq, map_one, one_mul]

Depends on / 依赖: ZMod.completedLFunction_modOne_eq, completedLFunction, completedLFunction_modOne_eq, map_one, one_mul
-/
lemma completedLFunction_modOne_eq {χ : DirichletCharacter Complex 1} :
    completedLFunction χ = completedRiemannZeta := by
  ext; rw [completedLFunction, ZMod.completedLFunction_modOne_eq, map_one, one_mul]

/--
lemma `differentiableAt_completedLFunction` / 引理 `differentiableAt_completedLFunction`

English:
lemma differentiableAt_completedLFunction
  statement: (χ : DirichletCharacter Complex N) (s : Complex)
  proof: ZMod.differentiableAt_completedLFunction _ _ (by have := χ.map_zero'; tauto)
    (by have := χ.sum_eq_zero_of_ne_one; tauto)

中文:
引理 differentiableAt_completedLFunction
  结论: (χ : DirichletCharacter 复形 N) (s : 复形)
  证明: ZMod.differentiableAt_completedLFunction _ _ (by have := χ.map_zero'; tauto)
    (by have := χ.sum_eq_zero_of_ne_one; tauto)

Depends on / 依赖: ZMod.differentiableAt_completedLFunction, differentiableAt_completedLFunction, map_zero, sum_eq_zero_of_ne_one
-/
lemma differentiableAt_completedLFunction (χ : DirichletCharacter Complex N) (s : Complex)
    (hs₀ : s != 0 ∨ N != 1) (hs₁ : s != 1 ∨ χ != 1) :
    DifferentiableAt Complex (completedLFunction χ) s :=
  ZMod.differentiableAt_completedLFunction _ _ (by have := χ.map_zero'; tauto)
    (by have := χ.sum_eq_zero_of_ne_one; tauto)

/--
lemma `differentiable_completedLFunction` / 引理 `differentiable_completedLFunction`

English:
lemma differentiable_completedLFunction
  given: {χ : DirichletCharacter Complex N} (hχ : χ != 1)
  proof: by
  refine fun s => differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ level_one' _

中文:
引理 differentiable_completedLFunction
  条件: {χ : DirichletCharacter 复形 N} (hχ : χ != 1)
  证明: by
  refine fun s => differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ level_one' _

Depends on / 依赖: Or.inr, differentiableAt_completedLFunction, level_one
-/
lemma differentiable_completedLFunction {χ : DirichletCharacter Complex N} (hχ : χ != 1) :
    Differentiable Complex (completedLFunction χ) := by
  refine fun s => differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ level_one' _

/--
lemma `LFunction_eq_completed_div_gammaFactor` / 引理 `LFunction_eq_completed_div_gammaFactor`

English:
lemma LFunction_eq_completed_div_gammaFactor
  statement: (χ : DirichletCharacter Complex N) (s : Complex)
  proof: by
  rcases χ.even_or_odd with hχ | hχ <;>
  rw [hχ.gammaFactor_def]
  · exact LFunction_eq_completed_div_gammaFactor_even hχ.to_fun _ (h.imp_right χ.map_zero')
  · apply LFunction_eq_completed_div_gammaFactor_odd hχ.to_fun

中文:
引理 LFunction_eq_completed_div_gammaFactor
  结论: (χ : DirichletCharacter 复形 N) (s : 复形)
  证明: by
  rcases χ.even_or_odd with hχ | hχ <;>
  rw [hχ.gammaFactor_def]
  · exact LFunction_eq_completed_div_gammaFactor_even hχ.to_fun _ (h.imp_right χ.map_zero')
  · apply LFunction_eq_completed_div_gammaFactor_odd hχ.to_fun

Depends on / 依赖: LFunction_eq_completed_div_gammaFactor_even, LFunction_eq_completed_div_gammaFactor_odd, even_or_odd, gammaFactor_def, h.imp_right, imp_right, map_zero, to_fun
-/
lemma LFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter Complex N) (s : Complex)
    (h : s != 0 ∨ N != 1) : LFunction χ s = completedLFunction χ s / gammaFactor χ s := by
  rcases χ.even_or_odd with hχ | hχ <;>
  rw [hχ.gammaFactor_def]
  · exact LFunction_eq_completed_div_gammaFactor_even hχ.to_fun _ (h.imp_right χ.map_zero')
  · apply LFunction_eq_completed_div_gammaFactor_odd hχ.to_fun

open scoped Classical in
/--
Definition of `rootNumber` / `rootNumber` 的定义

English:
definition rootNumber
  signature: (χ : DirichletCharacter Complex N)
  body: gaussSum χ stdAddChar / I ^ (if χ.Even then 0 else 1) / N ^ (1 / 2 : Complex)

中文:
定义 rootNumber
  签名: (χ : DirichletCharacter 复形 N)
  定义体: gaussSum χ stdAddChar / I ^ (if χ.Even then 0 else 1) / N ^ (1 / 2 : Complex)

Depends on / 依赖: gaussSum, stdAddChar
-/
noncomputable def rootNumber (χ : DirichletCharacter Complex N) : Complex :=
  gaussSum χ stdAddChar / I ^ (if χ.Even then 0 else 1) / N ^ (1 / 2 : Complex)

/--
lemma `rootNumber_modOne` / 引理 `rootNumber_modOne`

English:
lemma rootNumber_modOne
  given: (χ : DirichletCharacter Complex 1)
  statement: rootNumber χ = 1
  proof: by
  simp [rootNumber, gaussSum, -univ_unique, ← singleton_eq_univ (1 : ZMod 1),
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _),
    (show χ.Even from map_one _)]

中文:
引理 rootNumber_modOne
  条件: (χ : DirichletCharacter 复形 1)
  结论: rootNumber χ = 1
  证明: by
  simp [rootNumber, gaussSum, -univ_unique, ← singleton_eq_univ (1 : ZMod 1),
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _),
    (show χ.Even from map_one _)]

Depends on / 依赖: AddChar, AddChar.map_zero_eq_one, gaussSum, map_one, map_zero_eq_one, rootNumber, singleton_eq_univ, stdAddChar, univ_unique
-/
lemma rootNumber_modOne (χ : DirichletCharacter Complex 1) : rootNumber χ = 1 := by
  simp [rootNumber, gaussSum, -univ_unique, ← singleton_eq_univ (1 : ZMod 1),
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _),
    (show χ.Even from map_one _)]

namespace IsPrimitive

/--
theorem `completedLFunction_one_sub` / 定理 `completedLFunction_one_sub`

English:
theorem completedLFunction_one_sub
  given: {χ : DirichletCharacter Complex N} (hχ : IsPrimitive χ) (s : Complex)
  proof: by
  classical
  -- First handle special case of Riemann zeta
  rcases eq_or_ne N 1 with rfl | hN
  · simp [completedLFunction_modOne_eq, completedRiemannZeta_one_sub, rootNumber_modOne]
  -- facts about `χ` as function
  have h_sum : ∑ j, χ j = 0 := by
    refine χ.sum_eq_zero_of_ne_one (fun h => hN.symm ?_)
    rwa [IsPrimitive, h, conductor_one] at hχ
  let ε := I ^ (if χ.Even then 0 else 1)
  -- gather up powers of N
  rw [rootNumber]; rw [← mul_comm_div]; rw [← mul_comm_div]; rw [← cpow_sub _ _ (NeZero.ne _)]; rw [sub_sub]; rw [add_halves]
  calc completedLFunction χ (1 - s)
  _ = N ^ (s - 1) * χ (-1) / ε * ZMod.completedLFunction (𝓕 χ) s := by
    simp only [ε]
    split_ifs with h
    · rw [pow_zero, div_one, h, mul_one, completedLFunction,
        completedLFunction_one_sub_even h.to_fun _ (.inr h_sum) (.inr <| χ.map_zero' hN)]
    · replace h : χ.Odd := χ.even_or_odd.resolve_left h
      rw [completedLFunction]; rw [completedLFunction_one_sub_odd h.to_fun]; rw [pow_one]; rw [h]; rw [div_I]; rw [mul_neg_one]; rw [← neg_mul]; rw [neg_neg]
  _ = (_) * ZMod.completedLFunction (fun j => χ⁻¹ (-1) * gaussSum χ stdAddChar * χ⁻¹ j) s := by
    congr 2 with j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum]; rw [← neg_one_mul j]; rw [map_mul]; rw [mul_right_comm]
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s * (χ (-1) * χ⁻¹ (-1)) := by
    rw [completedLFunction]; rw [completedLFunction_const_mul]
    ring
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s := by
    rw [← MulChar.mul_apply]; rw [mul_inv_cancel]; rw [MulChar.one_apply (isUnit_one.neg)]; rw [mul_one]

中文:
定理 completedLFunction_one_sub
  条件: {χ : DirichletCharacter 复形 N} (hχ : 是Primitive χ) (s : 复形)
  证明: by
  classical
  -- First handle special case of Riemann zeta
  rcases eq_or_ne N 1 with rfl | hN
  · simp [completedLFunction_modOne_eq, completedRiemannZeta_one_sub, rootNumber_modOne]
  -- facts about `χ` as function
  have h_sum : ∑ j, χ j = 0 := by
    refine χ.sum_eq_zero_of_ne_one (fun h => hN.symm ?_)
    rwa [IsPrimitive, h, conductor_one] at hχ
  let ε := I ^ (if χ.Even then 0 else 1)
  -- gather up powers of N
  rw [rootNumber]; rw [← mul_comm_div]; rw [← mul_comm_div]; rw [← cpow_sub _ _ (NeZero.ne _)]; rw [sub_sub]; rw [add_halves]
  calc completedLFunction χ (1 - s)
  _ = N ^ (s - 1) * χ (-1) / ε * ZMod.completedLFunction (𝓕 χ) s := by
    simp only [ε]
    split_ifs with h
    · rw [pow_zero, div_one, h, mul_one, completedLFunction,
        completedLFunction_one_sub_even h.to_fun _ (.inr h_sum) (.inr <| χ.map_zero' hN)]
    · replace h : χ.Odd := χ.even_or_odd.resolve_left h
      rw [completedLFunction]; rw [completedLFunction_one_sub_odd h.to_fun]; rw [pow_one]; rw [h]; rw [div_I]; rw [mul_neg_one]; rw [← neg_mul]; rw [neg_neg]
  _ = (_) * ZMod.completedLFunction (fun j => χ⁻¹ (-1) * gaussSum χ stdAddChar * χ⁻¹ j) s := by
    congr 2 with j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum]; rw [← neg_one_mul j]; rw [map_mul]; rw [mul_right_comm]
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s * (χ (-1) * χ⁻¹ (-1)) := by
    rw [completedLFunction]; rw [completedLFunction_const_mul]
    ring
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s := by
    rw [← MulChar.mul_apply]; rw [mul_inv_cancel]; rw [MulChar.one_apply (isUnit_one.neg)]; rw [mul_one]

Depends on / 依赖: classical
-/
theorem completedLFunction_one_sub {χ : DirichletCharacter Complex N} (hχ : IsPrimitive χ) (s : Complex) :
    completedLFunction χ (1 - s) = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s := by
  classical
  -- First handle special case of Riemann zeta
  rcases eq_or_ne N 1 with rfl | hN
  · simp [completedLFunction_modOne_eq, completedRiemannZeta_one_sub, rootNumber_modOne]
  -- facts about `χ` as function
  have h_sum : ∑ j, χ j = 0 := by
    refine χ.sum_eq_zero_of_ne_one (fun h => hN.symm ?_)
    rwa [IsPrimitive, h, conductor_one] at hχ
  let ε := I ^ (if χ.Even then 0 else 1)
  -- gather up powers of N
  rw [rootNumber]; rw [← mul_comm_div]; rw [← mul_comm_div]; rw [← cpow_sub _ _ (NeZero.ne _)]; rw [sub_sub]; rw [add_halves]
  calc completedLFunction χ (1 - s)
  _ = N ^ (s - 1) * χ (-1) / ε * ZMod.completedLFunction (𝓕 χ) s := by
    simp only [ε]
    split_ifs with h
    · rw [pow_zero, div_one, h, mul_one, completedLFunction,
        completedLFunction_one_sub_even h.to_fun _ (.inr h_sum) (.inr <| χ.map_zero' hN)]
    · replace h : χ.Odd := χ.even_or_odd.resolve_left h
      rw [completedLFunction]; rw [completedLFunction_one_sub_odd h.to_fun]; rw [pow_one]; rw [h]; rw [div_I]; rw [mul_neg_one]; rw [← neg_mul]; rw [neg_neg]
  _ = (_) * ZMod.completedLFunction (fun j => χ⁻¹ (-1) * gaussSum χ stdAddChar * χ⁻¹ j) s := by
    congr 2 with j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum]; rw [← neg_one_mul j]; rw [map_mul]; rw [mul_right_comm]
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s * (χ (-1) * χ⁻¹ (-1)) := by
    rw [completedLFunction]; rw [completedLFunction_const_mul]
    ring
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s := by
    rw [← MulChar.mul_apply]; rw [mul_inv_cancel]; rw [MulChar.one_apply (isUnit_one.neg)]; rw [mul_one]

end IsPrimitive

end DirichletCharacter

/-!
### The logarithmic derivative of the L-function of a Dirichlet character

We show that `s ↦ -(L' χ s) / L χ s + 1 / (s - 1)` is continuous outside the zeros of `L χ`
when `χ` is a trivial Dirichlet character and that `-L' χ / L χ` is continuous outside
the zeros of `L χ` when `χ` is nontrivial.
-/

namespace DirichletCharacter

open Complex

section trivial

variable (n : Nat) [NeZero n]

/--
Definition of `LFunctionTrivChar₁` / `LFunctionTrivChar₁` 的定义

English:
abbreviation LFunctionTrivChar₁
  signature: : Complex -> Complex
  body: Function.update (fun s => (s - 1) * LFunctionTrivChar n s) 1
    (∏ p in n.primeFactors, (1 - (p : Complex)⁻¹))

中文:
缩写 LFunctionTrivChar₁
  签名: : 复形 -> 复形
  定义体: Function.update (fun s => (s - 1) * LFunctionTrivChar n s) 1
    (∏ p in n.primeFactors, (1 - (p : Complex)⁻¹))

Depends on / 依赖: Function, Function.update, LFunctionTrivChar, n.primeFactors, primeFactors, update
-/
noncomputable abbrev LFunctionTrivChar₁ : Complex -> Complex :=
  Function.update (fun s => (s - 1) * LFunctionTrivChar n s) 1
    (∏ p in n.primeFactors, (1 - (p : Complex)⁻¹))

/--
lemma `LFunctionTrivChar₁_apply_one_ne_zero` / 引理 `LFunctionTrivChar₁_apply_one_ne_zero`

English:
lemma LFunctionTrivChar₁_apply_one_ne_zero
  statement: LFunctionTrivChar₁ n 1 != 0
  proof: by
  simp only [Function.update_self]
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  simpa [sub_ne_zero] using (Nat.prime_of_mem_primeFactors hp).ne_one

中文:
引理 LFunctionTrivChar₁_apply_one_ne_zero
  结论: LFunctionTrivChar₁ n 1 != 0
  证明: by
  simp only [Function.update_self]
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  simpa [sub_ne_zero] using (Nat.prime_of_mem_primeFactors hp).ne_one

Depends on / 依赖: Finset, Finset.prod_ne_zero_iff.mpr, Function, Function.update_self, Nat.prime_of_mem_primeFactors, ne_one, prime_of_mem_primeFactors, prod_ne_zero_iff, sub_ne_zero, update_self
-/
lemma LFunctionTrivChar₁_apply_one_ne_zero : LFunctionTrivChar₁ n 1 != 0 := by
  simp only [Function.update_self]
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  simpa [sub_ne_zero] using (Nat.prime_of_mem_primeFactors hp).ne_one

/--
lemma `differentiable_LFunctionTrivChar₁` / 引理 `differentiable_LFunctionTrivChar₁`

English:
lemma differentiable_LFunctionTrivChar₁
  statement: Differentiable Complex (LFunctionTrivChar₁ n)
  proof: by
  rw [← differentiableOn_univ]; rw [← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun s => (s - 1) * LFunctionTrivChar n s)
    (fun _ hs => DifferentiableAt.differentiableWithinAt <| by fun_prop (disch := simp_all))
    fun _ hs => Function.update_of_ne (Set.mem_sdiff_singleton.mp hs).2 ..,
    continuousWithinAt_compl_self.mp ?_⟩
  simpa using LFunctionTrivChar_residue_one

中文:
引理 differentiable_LFunctionTrivChar₁
  结论: 可微 复形 (LFunctionTrivChar₁ n)
  证明: by
  rw [← differentiableOn_univ]; rw [← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun s => (s - 1) * LFunctionTrivChar n s)
    (fun _ hs => DifferentiableAt.differentiableWithinAt <| by fun_prop (disch := simp_all))
    fun _ hs => Function.update_of_ne (Set.mem_sdiff_singleton.mp hs).2 ..,
    continuousWithinAt_compl_self.mp ?_⟩
  simpa using LFunctionTrivChar_residue_one

Depends on / 依赖: DifferentiableAt, DifferentiableAt.differentiableWithinAt, DifferentiableOn, DifferentiableOn.congr, Filter, Filter.univ_mem, Function, Function.update_of_ne, LFunctionTrivChar, LFunctionTrivChar_residue_one, Set.mem_sdiff_singleton.mp, continuousWithinAt_compl_self, continuousWithinAt_compl_self.mp, differentiableOn_compl_singleton_and_continuousAt_iff, differentiableOn_univ, differentiableWithinAt, fun_prop, mem_sdiff_singleton, univ_mem, update_of_ne
-/
lemma differentiable_LFunctionTrivChar₁ : Differentiable Complex (LFunctionTrivChar₁ n) := by
  rw [← differentiableOn_univ]; rw [← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun s => (s - 1) * LFunctionTrivChar n s)
    (fun _ hs => DifferentiableAt.differentiableWithinAt <| by fun_prop (disch := simp_all))
    fun _ hs => Function.update_of_ne (Set.mem_sdiff_singleton.mp hs).2 ..,
    continuousWithinAt_compl_self.mp ?_⟩
  simpa using LFunctionTrivChar_residue_one

/--
lemma `deriv_LFunctionTrivChar₁_apply_of_ne_one` / 引理 `deriv_LFunctionTrivChar₁_apply_of_ne_one`

English:
lemma deriv_LFunctionTrivChar₁_apply_of_ne_one
  given: {s : Complex} (hs : s != 1)
  proof: by
  have H : deriv (LFunctionTrivChar₁ n) s =
      deriv (fun w => (w - 1) * LFunctionTrivChar n w) s := by
.deriv_eq refine eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨_, isOpen_ne.mem_nhds hs, fun _ hw => Function.update_of_ne (Set.mem_ofPred.mp hw) ..⟩
  rw [H]; rw [deriv_fun_mul (by fun_prop) (differentiableAt_LFunction _ s (.inl hs))]; rw [deriv_sub_const]; rw [deriv_id'']; rw [one_mul]; rw [add_comm]

中文:
引理 deriv_LFunctionTrivChar₁_apply_of_ne_one
  条件: {s : 复形} (hs : s != 1)
  证明: by
  have H : deriv (LFunctionTrivChar₁ n) s =
      deriv (fun w => (w - 1) * LFunctionTrivChar n w) s := by
.deriv_eq refine eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨_, isOpen_ne.mem_nhds hs, fun _ hw => Function.update_of_ne (Set.mem_ofPred.mp hw) ..⟩
  rw [H]; rw [deriv_fun_mul (by fun_prop) (differentiableAt_LFunction _ s (.inl hs))]; rw [deriv_sub_const]; rw [deriv_id'']; rw [one_mul]; rw [add_comm]

Depends on / 依赖: Function, Function.update_of_ne, LFunctionTrivChar, Set.mem_ofPred.mp, add_comm, deriv_eq, deriv_fun_mul, deriv_id, deriv_sub_const, differentiableAt_LFunction, eventuallyEq_iff_exists_mem, eventuallyEq_iff_exists_mem.mpr, fun_prop, isOpen_ne, isOpen_ne.mem_nhds, mem_nhds, mem_ofPred, one_mul, update_of_ne
-/
lemma deriv_LFunctionTrivChar₁_apply_of_ne_one {s : Complex} (hs : s != 1) :
    deriv (LFunctionTrivChar₁ n) s =
      (s - 1) * deriv (LFunctionTrivChar n) s + LFunctionTrivChar n s := by
  have H : deriv (LFunctionTrivChar₁ n) s =
      deriv (fun w => (w - 1) * LFunctionTrivChar n w) s := by
.deriv_eq refine eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨_, isOpen_ne.mem_nhds hs, fun _ hw => Function.update_of_ne (Set.mem_ofPred.mp hw) ..⟩
  rw [H]; rw [deriv_fun_mul (by fun_prop) (differentiableAt_LFunction _ s (.inl hs))]; rw [deriv_sub_const]; rw [deriv_id'']; rw [one_mul]; rw [add_comm]

/--
lemma `continuousOn_neg_logDeriv_LFunctionTrivChar₁` / 引理 `continuousOn_neg_logDeriv_LFunctionTrivChar₁`

English:
lemma continuousOn_neg_logDeriv_LFunctionTrivChar₁
  proof: by
  simp_rw [neg_div]
  have h := differentiable_LFunctionTrivChar₁ n
  refine ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun w hw => ?_).neg
  rcases eq_or_ne w 1 with rfl | hw'
  · exact LFunctionTrivChar₁_apply_one_ne_zero _
  · rw [LFunctionTrivChar₁, Function.update_of_ne hw', mul_ne_zero_iff]
    exact ⟨sub_ne_zero_of_ne hw', (Set.mem_ofPred.mp hw).resolve_left hw'⟩

中文:
引理 continuousOn_neg_logDeriv_LFunctionTrivChar₁
  证明: by
  simp_rw [neg_div]
  have h := differentiable_LFunctionTrivChar₁ n
  refine ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun w hw => ?_).neg
  rcases eq_or_ne w 1 with rfl | hw'
  · exact LFunctionTrivChar₁_apply_one_ne_zero _
  · rw [LFunctionTrivChar₁, Function.update_of_ne hw', mul_ne_zero_iff]
    exact ⟨sub_ne_zero_of_ne hw', (Set.mem_ofPred.mp hw).resolve_left hw'⟩

Depends on / 依赖: Function, Function.update_of_ne, Set.mem_ofPred.mp, contDiff, continuous, continuousOn, continuousOn.div, continuous_deriv, eq_or_ne, h.contDiff.continuous_deriv, h.continuous.continuousOn, le_rfl, mem_ofPred, mul_ne_zero_iff, neg_div, resolve_left, simp_rw, sub_ne_zero_of_ne, update_of_ne
-/
lemma continuousOn_neg_logDeriv_LFunctionTrivChar₁ :
    ContinuousOn (fun s => -deriv (LFunctionTrivChar₁ n) s / LFunctionTrivChar₁ n s)
      {s | s = 1 ∨ LFunctionTrivChar n s != 0} := by
  simp_rw [neg_div]
  have h := differentiable_LFunctionTrivChar₁ n
  refine ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun w hw => ?_).neg
  rcases eq_or_ne w 1 with rfl | hw'
  · exact LFunctionTrivChar₁_apply_one_ne_zero _
  · rw [LFunctionTrivChar₁, Function.update_of_ne hw', mul_ne_zero_iff]
    exact ⟨sub_ne_zero_of_ne hw', (Set.mem_ofPred.mp hw).resolve_left hw'⟩

end trivial

section nontrivial

variable {n : Nat} [NeZero n] {χ : DirichletCharacter Complex n}

/--
lemma `continuousOn_neg_logDeriv_LFunction_of_nontriv` / 引理 `continuousOn_neg_logDeriv_LFunction_of_nontriv`

English:
lemma continuousOn_neg_logDeriv_LFunction_of_nontriv
  given: (hχ : χ != 1)
  proof: by
  have h := differentiable_LFunction hχ
  simpa [neg_div] using! ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun _ hw => hw).fun_neg

中文:
引理 continuousOn_neg_logDeriv_LFunction_of_nontriv
  条件: (hχ : χ != 1)
  证明: by
  have h := differentiable_LFunction hχ
  simpa [neg_div] using! ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun _ hw => hw).fun_neg

Depends on / 依赖: contDiff, continuous, continuousOn, continuousOn.div, continuous_deriv, differentiable_LFunction, fun_neg, h.contDiff.continuous_deriv, h.continuous.continuousOn, le_rfl, neg_div
-/
lemma continuousOn_neg_logDeriv_LFunction_of_nontriv (hχ : χ != 1) :
    ContinuousOn (fun s => -deriv (LFunction χ) s / LFunction χ s) {s | LFunction χ s != 0} := by
  have h := differentiable_LFunction hχ
  simpa [neg_div] using! ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun _ hw => hw).fun_neg

end nontrivial

end DirichletCharacter
