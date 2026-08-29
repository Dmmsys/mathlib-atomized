/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.SummableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.EMetricSpace.Paracompact

/-!
# Eisenstein series q-expansions

We give the q-expansion of Eisenstein series of weight `k` and level 1. In particular, we prove
`EisensteinSeries.q_expansion_bernoulli` which says that for even `k` with `3 ≤ k`
Eisenstein series can be written as `1 - (2k / bernoulli k) ∑' n, σ_{k-1}(n) q^n` where
`q = exp(2πiz)` and `σ_{k-1}(n)` is the sum of the `(k-1)`-th powers of the divisors of `n`.
We need `k` to be even so that the Eisenstein series are non-zero and we require `k ≥ 3` so that
the series converges absolutely.

We also identify the q-expansion coefficients as a `PowerSeries` via
`EisensteinSeries.E_qExpansion_coeff`, and use this to prove that the normalised Eisenstein series
is non-zero (`EisensteinSeries.E_ne_zero`).

The proof relies on the identity
`∑' n : ℤ, 1 / (z + n) ^ (k + 1) = ((-2πi)^(k+1) / k!) ∑' n : ℕ, n^k q^n` which comes from
differentiating the expansion of `π cot(πz)` in terms of exponentials. Since our Eisenstein series
are defined as sums over coprime integer pairs, we also need to relate these to sums over all pairs
of integers, which is done in `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`. This then
gives the q-expansion with a Riemann zeta factor, which we simplify using the formula for
`ζ(k)` in terms of Bernoulli numbers to get the final result.

-/

public section

open Set Metric TopologicalSpace Function Filter Complex ArithmeticFunction
  ModularForm EisensteinSeries

open scoped Real Nat ArithmeticFunction.sigma

open UpperHalfPlane hiding I

local notation "ℍₒ" => upperHalfPlaneSet

/--
lemma `iteratedDerivWithin_cexp_aux` / 引理 `iteratedDerivWithin_cexp_aux`

English:
lemma iteratedDerivWithin_cexp_aux
  given: (k m : Nat) (p : Real) {S : Set Complex} (hs : IsOpen S)
  proof: by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  intro x hx
  have : (fun s => cexp (2 * π * I * m * s / p)) = fun s => cexp (((2 * π * I * m) / p) * s) := by
    ext z
    ring_nf
  simp only [this, iteratedDeriv_cexp_const_mul]
  ring_nf

中文:
引理 iteratedDerivWithin_cexp_aux
  条件: (k m : 自然数) (p : 实数) {S : Set Complex} (hs : IsOpen S)
  证明: by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  intro x hx
  have : (fun s => cexp (2 * π * I * m * s / p)) = fun s => cexp (((2 * π * I * m) / p) * s) := by
    ext z
    ring_nf
  simp only [this, iteratedDeriv_cexp_const_mul]
  ring_nf
-/
private lemma iteratedDerivWithin_cexp_aux (k m : Nat) (p : Real) {S : Set Complex} (hs : IsOpen S) :
    EqOn (iteratedDerivWithin k (fun s : Complex => cexp (2 * π * I * m * s / p)) S)
    (fun s => (2 * π * I * m / p) ^ k * cexp (2 * π * I * m * s / p)) S := by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  intro x hx
  have : (fun s => cexp (2 * π * I * m * s / p)) = fun s => cexp (((2 * π * I * m) / p) * s) := by
    ext z
    ring_nf
  simp only [this, iteratedDeriv_cexp_const_mul]
  ring_nf

/--
lemma `aux_IsBigO_mul` / 引理 `aux_IsBigO_mul`

English:
lemma aux_IsBigO_mul
  statement: (k l : Nat) (p : Real) {f : Nat -> Complex}
  proof: by
  have h0 : (fun n : Nat => (2 * π * I * n / p) ^ k) =O[atTop] fun n => ((n ^ k) : Real) := by
    have h1 : (fun n : Nat => (2 * π * I * n / p) ^ k) =
        fun n : Nat => ((2 * π * I / p) ^ k) * n ^ k := by
      ext z
      ring
    simpa [h1] using isBigO_ofReal_right.mp (Asymptotics.isBigO

中文:
引理 aux_IsBigO_mul
  结论: (k l : 自然数) (p : 实数) {f : 自然数 -> Complex}
  证明: by
  have h0 : (fun n : Nat => (2 * π * I * n / p) ^ k) =O[atTop] fun n => ((n ^ k) : Real) := by
    have h1 : (fun n : Nat => (2 * π * I * n / p) ^ k) =
        fun n : Nat => ((2 * π * I / p) ^ k) * n ^ k := by
      ext z
      ring
    simpa [h1] using isBigO_ofReal_right.mp (Asymptotics.isBigO
-/
private lemma aux_IsBigO_mul (k l : Nat) (p : Real) {f : Nat -> Complex}
    (hf : f =O[atTop] fun n => ((n ^ l) : Real)) :
    (fun n => f n * (2 * π * I * n / p) ^ k) =O[atTop] fun n => (↑(n ^ (l + k)) : Real) := by
  have h0 : (fun n : Nat => (2 * π * I * n / p) ^ k) =O[atTop] fun n => ((n ^ k) : Real) := by
    have h1 : (fun n : Nat => (2 * π * I * n / p) ^ k) =
        fun n : Nat => ((2 * π * I / p) ^ k) * n ^ k := by
      ext z
      ring
    simpa [h1] using isBigO_ofReal_right.mp (Asymptotics.isBigO_const_mul_self
      ((2 * π * I / p) ^ k) (fun (n : Nat) => (↑(n ^ k) : Real)) atTop)
  push_cast
  convert! hf.mul h0
  ring

open BoundedContinuousFunction in
/--
theorem `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp` / 定理 `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp`

English:
theorem summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp
  statement: (k l : Nat) {f : Nat -> Complex} {p : Real}
  proof: by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  have : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K Complex := ⟨fun r : K => Complex.exp (2 * π * I * r / p), by fun_prop⟩
  let r : Real :=

中文:
定理 summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp
  结论: (k l : 自然数) {f : 自然数 -> Complex} {p : 实数}
  证明: by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  have : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K Complex := ⟨fun r : K => Complex.exp (2 * π * I * r / p), by fun_prop⟩
  let r : Real :=

Depends on / 依赖: CompactSpace, Complex.exp, ContinuousMap, ContinuousMap.coe_mk, Real.zero_lt_one, SummableLocallyUniformlyOn_of_locally_bounded, coe_mk, fun_prop, isCompact_iff_isCompact_univ, isCompact_iff_isCompact_univ.mp, isCompact_univ_iff, isCompact_univ_iff.mp, isOpen_upperHalfPlaneSet, mkOfCompact, mkOfCompact_apply, norm_lt_iff_of_compact, norm_norm, zero_lt_one
-/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp (k l : Nat) {f : Nat -> Complex} {p : Real}
    (hp : 0 < p) (hf : f =O[atTop] (fun n => ((n ^ l) : Real))) :
    SummableLocallyUniformlyOn (fun n => (f n) •
      iteratedDerivWithin k (fun z => cexp (2 * π * I * z / p) ^ n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  have : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K Complex := ⟨fun r : K => Complex.exp (2 * π * I * r / p), by fun_prop⟩
  let r : Real := ‖mkOfCompact c‖
  have hr : ‖r‖ < 1 := by
    simp only [norm_norm, r, norm_lt_iff_of_compact Real.zero_lt_one, mkOfCompact_apply,
      ContinuousMap.coe_mk, c]
    intro x
    have h1 : cexp (2 * π * I * (x / p)) = cexp (2 * π * I * x / p) := by
      ring_nf
    simpa using h1 ▸ norm_exp_two_pi_I_lt_one ⟨((x : Complex) / p), by aesop⟩
  refine ⟨_, by simpa using (summable_norm_mul_geometric_of_norm_lt_one' hr
    (Asymptotics.isBigO_norm_left.mpr (aux_IsBigO_mul k l p hf))), fun n z hz => ?_⟩
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (norm_coe_le_norm (mkOfCompact c) ⟨z, hz⟩) n
  simp only [norm_mkOfCompact, mkOfCompact_apply, ContinuousMap.coe_mk, ← exp_nsmul', Pi.smul_apply,
    iteratedDerivWithin_cexp_aux k n p isOpen_upperHalfPlaneSet (hK hz), smul_eq_mul,
    norm_mul, norm_pow, Complex.norm_div, norm_ofNat, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    norm_natCast, abs_norm, ge_iff_le, r, c] at *
  rw [← mul_assoc]
  gcongr
  convert! h0
  rw [← norm_pow]; rw [← exp_nsmul']

/--
theorem `summableLocallyUniformlyOn_iteratedDerivWithin_cexp` / 定理 `summableLocallyUniformlyOn_iteratedDerivWithin_cexp`

English:
theorem summableLocallyUniformlyOn_iteratedDerivWithin_cexp
  given: (k : Nat)
  proof: by
  have h0 : (fun n : Nat => (1 : Complex)) =O[atTop] fun n => ((n ^ 1) : Real) := by
    simp only [Asymptotics.isBigO_iff, norm_one, norm_pow, Real.norm_natCast, eventually_atTop]
    exact ⟨1, 1, fun b hb => by norm_cast; simp [hb]⟩
  simpa using summableLocallyUniformlyOn_iteratedDerivWithin_s

中文:
定理 summableLocallyUniformlyOn_iteratedDerivWithin_cexp
  条件: (k : 自然数)
  证明: by
  have h0 : (fun n : Nat => (1 : Complex)) =O[atTop] fun n => ((n ^ 1) : Real) := by
    simp only [Asymptotics.isBigO_iff, norm_one, norm_pow, Real.norm_natCast, eventually_atTop]
    exact ⟨1, 1, fun b hb => by norm_cast; simp [hb]⟩
  simpa using summableLocallyUniformlyOn_iteratedDerivWithin_s

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_iff, Real.norm_natCast, eventually_atTop, isBigO_iff, norm_natCast, norm_one, norm_pow, summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp
-/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_cexp (k : Nat) :
    SummableLocallyUniformlyOn
      (fun n => iteratedDerivWithin k (fun z => cexp (2 * π * I * z) ^ n) ℍₒ) ℍₒ := by
  have h0 : (fun n : Nat => (1 : Complex)) =O[atTop] fun n => ((n ^ 1) : Real) := by
    simp only [Asymptotics.isBigO_iff, norm_one, norm_pow, Real.norm_natCast, eventually_atTop]
    exact ⟨1, 1, fun b hb => by norm_cast; simp [hb]⟩
  simpa using summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp k 1 (p := 1)
    (by norm_num) h0

/--
lemma `differentiableAt_iteratedDerivWithin_cexp` / 引理 `differentiableAt_iteratedDerivWithin_cexp`

English:
lemma differentiableAt_iteratedDerivWithin_cexp
  statement: (n a : Nat) {s : Set Complex} (hs : IsOpen s)
  proof: by
  apply DifferentiableOn.differentiableAt _ (hs.mem_nhds hr)
  suffices DifferentiableOn Complex (iteratedDeriv a (fun z => cexp (2 * π * I * z) ^ n)) s by
    apply this.congr (iteratedDerivWithin_of_isOpen hs)
  fun_prop

中文:
引理 differentiableAt_iteratedDerivWithin_cexp
  结论: (n a : 自然数) {s : Set Complex} (hs : IsOpen s)
  证明: by
  apply DifferentiableOn.differentiableAt _ (hs.mem_nhds hr)
  suffices DifferentiableOn Complex (iteratedDeriv a (fun z => cexp (2 * π * I * z) ^ n)) s by
    apply this.congr (iteratedDerivWithin_of_isOpen hs)
  fun_prop

Depends on / 依赖: DifferentiableOn, DifferentiableOn.differentiableAt, differentiableAt, fun_prop, hs.mem_nhds, iteratedDeriv, iteratedDerivWithin_of_isOpen, mem_nhds, this.congr
-/
lemma differentiableAt_iteratedDerivWithin_cexp (n a : Nat) {s : Set Complex} (hs : IsOpen s)
    {r : Complex} (hr : r in s) : DifferentiableAt Complex
      (iteratedDerivWithin a (fun z => cexp (2 * π * I * z) ^ n) s) r := by
  apply DifferentiableOn.differentiableAt _ (hs.mem_nhds hr)
  suffices DifferentiableOn Complex (iteratedDeriv a (fun z => cexp (2 * π * I * z) ^ n)) s by
    apply this.congr (iteratedDerivWithin_of_isOpen hs)
  fun_prop

/--
lemma `iteratedDerivWithin_tsum_cexp_eq` / 引理 `iteratedDerivWithin_tsum_cexp_eq`

English:
lemma iteratedDerivWithin_tsum_cexp_eq
  given: (k : Nat) (z : ℍ)
  proof: by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet (by simpa using z.2)]
  · exact fun x hx => summable_geometric_iff_norm_lt_one.mpr
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)
  · exact fun n _ _ => summableLocallyUniformlyOn_iteratedDerivWithin_cexp n
  · exact fun n l z hl 

中文:
引理 iteratedDerivWithin_tsum_cexp_eq
  条件: (k : 自然数) (z : ℍ)
  证明: by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet (by simpa using z.2)]
  · exact fun x hx => summable_geometric_iff_norm_lt_one.mpr
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)
  · exact fun n _ _ => summableLocallyUniformlyOn_iteratedDerivWithin_cexp n
  · exact fun n l z hl 

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.norm_exp_two_pi_I_lt_one, differentiableAt_iteratedDerivWithin_cexp, isOpen_upperHalfPlaneSet, iteratedDerivWithin_tsum, norm_exp_two_pi_I_lt_one, summableLocallyUniformlyOn_iteratedDerivWithin_cexp, summable_geometric_iff_norm_lt_one, summable_geometric_iff_norm_lt_one.mpr
-/
lemma iteratedDerivWithin_tsum_cexp_eq (k : Nat) (z : ℍ) :
    iteratedDerivWithin k (fun z => ∑' n : Nat, cexp (2 * π * I * z) ^ n) ℍₒ z =
    ∑' n : Nat, iteratedDerivWithin k (fun s : Complex => cexp (2 * π * I * s) ^ n) ℍₒ z := by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet (by simpa using z.2)]
  · exact fun x hx => summable_geometric_iff_norm_lt_one.mpr
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)
  · exact fun n _ _ => summableLocallyUniformlyOn_iteratedDerivWithin_cexp n
  · exact fun n l z hl hz => differentiableAt_iteratedDerivWithin_cexp n l
      isOpen_upperHalfPlaneSet hz

/--
lemma `contDiffOn_tsum_cexp` / 引理 `contDiffOn_tsum_cexp`

English:
lemma contDiffOn_tsum_cexp
  given: (k : Nat∞)
  proof: contDiffOn_of_differentiableOn_deriv fun m _ z hz =>
  (((summableLocallyUniformlyOn_iteratedDerivWithin_cexp m).differentiableOn
  isOpen_upperHalfPlaneSet (fun n _ hz => differentiableAt_iteratedDerivWithin_cexp n m
  isOpen_upperHalfPlaneSet hz)) z hz).congr (fun z hz => iteratedDerivWithin_tsum_

中文:
引理 contDiffOn_tsum_cexp
  条件: (k : 自然数∞)
  证明: contDiffOn_of_differentiableOn_deriv fun m _ z hz =>
  (((summableLocallyUniformlyOn_iteratedDerivWithin_cexp m).differentiableOn
  isOpen_upperHalfPlaneSet (fun n _ hz => differentiableAt_iteratedDerivWithin_cexp n m
  isOpen_upperHalfPlaneSet hz)) z hz).congr (fun z hz => iteratedDerivWithin_tsum_

Depends on / 依赖: contDiffOn_of_differentiableOn_deriv, differentiableAt_iteratedDerivWithin_cexp, differentiableOn, isOpen_upperHalfPlaneSet, iteratedDerivWithin_tsum_cexp_eq, summableLocallyUniformlyOn_iteratedDerivWithin_cexp
-/
lemma contDiffOn_tsum_cexp (k : Nat∞) :
    ContDiffOn Complex k (fun z : Complex => ∑' n : Nat, cexp (2 * π * I * z) ^ n) ℍₒ :=
  contDiffOn_of_differentiableOn_deriv fun m _ z hz =>
  (((summableLocallyUniformlyOn_iteratedDerivWithin_cexp m).differentiableOn
  isOpen_upperHalfPlaneSet (fun n _ hz => differentiableAt_iteratedDerivWithin_cexp n m
  isOpen_upperHalfPlaneSet hz)) z hz).congr (fun z hz => iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)
  (iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)

/--
lemma `iteratedDerivWithin_tsum_exp_aux_eq` / 引理 `iteratedDerivWithin_tsum_exp_aux_eq`

English:
lemma iteratedDerivWithin_tsum_exp_aux_eq
  given: {k : Nat} (hk : 1 <= k) (z : ℍ)
  proof: by
  have : iteratedDerivWithin k (fun z => ((π * I) -
    (2 * π * I) * ∑' n : Nat, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) * ∑' n : Nat, iteratedDerivWithin k (fun s : Complex => cexp (2 * π * I * s) ^ n) ℍₒ z := by
    rw [iteratedDerivWithin_const_sub hk]; rw [iteratedDerivWithin_fun_

中文:
引理 iteratedDerivWithin_tsum_exp_aux_eq
  条件: {k : 自然数} (hk : 1 <= k) (z : ℍ)
  证明: by
  have : iteratedDerivWithin k (fun z => ((π * I) -
    (2 * π * I) * ∑' n : Nat, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) * ∑' n : Nat, iteratedDerivWithin k (fun s : Complex => cexp (2 * π * I * s) ^ n) ℍₒ z := by
    rw [iteratedDerivWithin_const_sub hk]; rw [iteratedDerivWithin_fun_
-/
private lemma iteratedDerivWithin_tsum_exp_aux_eq {k : Nat} (hk : 1 <= k) (z : ℍ) :
    iteratedDerivWithin k (fun z => ((π * I) -
    (2 * π * I) * ∑' n : Nat, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) ^ (k + 1) * ∑' n : Nat, n ^ k * cexp (2 * π * I * z) ^ n := by
  have : iteratedDerivWithin k (fun z => ((π * I) -
    (2 * π * I) * ∑' n : Nat, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) * ∑' n : Nat, iteratedDerivWithin k (fun s : Complex => cexp (2 * π * I * s) ^ n) ℍₒ z := by
    rw [iteratedDerivWithin_const_sub hk]; rw [iteratedDerivWithin_fun_neg]; rw [iteratedDerivWithin_const_mul (by simpa using z.2) (isOpen_upperHalfPlaneSet.uniqueDiffOn)]
    · simp only [iteratedDerivWithin_tsum_cexp_eq, neg_mul]
    · exact (contDiffOn_tsum_cexp k).contDiffWithinAt (by simpa using z.2)
  have h : -(2 * π * I * (2 * π * I) ^ k) * ∑' (n : Nat), n ^ k * cexp (2 * π * I * z) ^ n =
        -(2 * π * I) * ∑' n : Nat, (2 * π * I * n) ^ k * cexp (2 * π * I * z) ^ n := by
    simp_rw [← tsum_mul_left]
    congr
    ext y
    ring
  simp only [this, neg_mul, pow_succ', h, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
    OfNat.ofNat_ne_zero, ofReal_eq_zero, Real.pi_ne_zero, or_self, I_ne_zero, or_false]
  congr
  ext n
  have := exp_nsmul' (p := 1) (a := 2 * π * I) (n := n)
  simp_rw [div_one] at this
  simpa [this, UpperHalfPlane.coe] using
    iteratedDerivWithin_cexp_aux k n 1 isOpen_upperHalfPlaneSet z.2

/--
theorem `EisensteinSeries.qExpansion_identity` / 定理 `EisensteinSeries.qExpansion_identity`

English:
theorem EisensteinSeries.qExpansion_identity
  given: {k : Nat} (hk : 1 <= k) (z : ℍ)
  proof: by
  have : (-1) ^ k * k ! * ∑' n : Int, 1 / ((z : Complex) + n) ^ (k + 1) =
    -(2 * π * I) ^ (k + 1) * ∑' n : Nat, n ^ k * cexp (2 * π * I * z) ^ n := by
    rw [← iteratedDerivWithin_tsum_exp_aux_eq hk z]; rw [← iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hk (by simpa using z.2)]
    exac

中文:
定理 EisensteinSeries.qExpansion_identity
  条件: {k : 自然数} (hk : 1 <= k) (z : ℍ)
  证明: by
  have : (-1) ^ k * k ! * ∑' n : Int, 1 / ((z : Complex) + n) ^ (k + 1) =
    -(2 * π * I) ^ (k + 1) * ∑' n : Nat, n ^ k * cexp (2 * π * I * z) ^ n := by
    rw [← iteratedDerivWithin_tsum_exp_aux_eq hk z]; rw [← iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hk (by simpa using z.2)]
    exac

Depends on / 依赖: Nat.factorial_ne_zero, factorial_ne_zero, iteratedDerivWithin_congr, iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow, iteratedDerivWithin_tsum_exp_aux_eq, pi_mul_cot_pi_q_exp, simp_rw, tsum_mul_left
-/
theorem EisensteinSeries.qExpansion_identity {k : Nat} (hk : 1 <= k) (z : ℍ) :
    ∑' n : Int, 1 / ((z : Complex) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !) *
    ∑' n : Nat, n ^ k * cexp (2 * π * I * z) ^ n := by
  have : (-1) ^ k * k ! * ∑' n : Int, 1 / ((z : Complex) + n) ^ (k + 1) =
    -(2 * π * I) ^ (k + 1) * ∑' n : Nat, n ^ k * cexp (2 * π * I * z) ^ n := by
    rw [← iteratedDerivWithin_tsum_exp_aux_eq hk z]; rw [← iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hk (by simpa using z.2)]
    exact iteratedDerivWithin_congr (fun x hx => by (simpa using pi_mul_cot_pi_q_exp ⟨x, hx⟩))
      (by simpa using z.2)
  simp_rw [(eq_inv_mul_iff_mul_eq₀ (by simp [Nat.factorial_ne_zero])).mpr this, ← tsum_mul_left]
  congr
  ext n
  rw [show (-2 * π * I) ^ (k + 1) = (-1) ^ (k + 1) * (2 * π * I) ^ (k + 1) by rw [← neg_pow]; ring]
  field_simp
  ring_nf
  simp [Nat.mul_two]

/--
lemma `summable_pow_mul_cexp` / 引理 `summable_pow_mul_cexp`

English:
lemma summable_pow_mul_cexp
  given: (k : Nat) (e : Nat+) (z : ℍ)
  proof: by
  have he : 0 < (e * (z : Complex)).im := by
    simpa using z.2
  apply ((summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp 0 k (p := 1)
    (f := fun n => (n ^ k : Complex)) (by norm_num)
    (by simp [← Complex.isBigO_ofReal_right, Asymptotics.isBigO_refl])).summable he).congr
  grind [

中文:
引理 summable_pow_mul_cexp
  条件: (k : 自然数) (e : 自然数+) (z : ℍ)
  证明: by
  have he : 0 < (e * (z : Complex)).im := by
    simpa using z.2
  apply ((summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp 0 k (p := 1)
    (f := fun n => (n ^ k : Complex)) (by norm_num)
    (by simp [← Complex.isBigO_ofReal_right, Asymptotics.isBigO_refl])).summable he).congr
  grind [

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_refl, Complex.isBigO_ofReal_right, Pi.smul_apply, isBigO_ofReal_right, isBigO_refl, iteratedDerivWithin_zero, ofReal_one, smul_apply, smul_eq_mul, summable, summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp
-/
lemma summable_pow_mul_cexp (k : Nat) (e : Nat+) (z : ℍ) :
    Summable fun c : Nat => (c : Complex) ^ k * cexp (2 * π * I * e * z) ^ c := by
  have he : 0 < (e * (z : Complex)).im := by
    simpa using z.2
  apply ((summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp 0 k (p := 1)
    (f := fun n => (n ^ k : Complex)) (by norm_num)
    (by simp [← Complex.isBigO_ofReal_right, Asymptotics.isBigO_refl])).summable he).congr
  grind [ofReal_one, iteratedDerivWithin_zero, Pi.smul_apply, smul_eq_mul]

/--
theorem `EisensteinSeries.qExpansion_identity_pnat` / 定理 `EisensteinSeries.qExpansion_identity_pnat`

English:
theorem EisensteinSeries.qExpansion_identity_pnat
  given: {k : Nat} (hk : 1 <= k) (z : ℍ)
  proof: by
  rw [EisensteinSeries.qExpansion_identity hk z]; rw [← tsum_zero_pnat_eq_tsum_nat]
  · simp [show k != 0 by grind]
  · apply (summable_pow_mul_cexp k 1 z).congr
    simp

中文:
定理 EisensteinSeries.qExpansion_identity_pnat
  条件: {k : 自然数} (hk : 1 <= k) (z : ℍ)
  证明: by
  rw [EisensteinSeries.qExpansion_identity hk z]; rw [← tsum_zero_pnat_eq_tsum_nat]
  · simp [show k != 0 by grind]
  · apply (summable_pow_mul_cexp k 1 z).congr
    simp

Depends on / 依赖: EisensteinSeries, EisensteinSeries.qExpansion_identity, qExpansion_identity, summable_pow_mul_cexp, tsum_zero_pnat_eq_tsum_nat
-/
theorem EisensteinSeries.qExpansion_identity_pnat {k : Nat} (hk : 1 <= k) (z : ℍ) :
    ∑' n : Int, 1 / ((z : Complex) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !) *
    ∑' n : Nat+, n ^ k * cexp (2 * π * I * z) ^ (n : Nat) := by
  rw [EisensteinSeries.qExpansion_identity hk z]; rw [← tsum_zero_pnat_eq_tsum_nat]
  · simp [show k != 0 by grind]
  · apply (summable_pow_mul_cexp k 1 z).congr
    simp

/--
lemma `summable_eisSummand` / 引理 `summable_eisSummand`

English:
lemma summable_eisSummand
  given: {k : Nat} (hk : 3 <= k) (z : ℍ)
  proof: summable_norm_iff.mp summable_norm_eisSummand (Int.toNat_le.mp hk) z

中文:
引理 summable_eisSummand
  条件: {k : 自然数} (hk : 3 <= k) (z : ℍ)
  证明: summable_norm_iff.mp summable_norm_eisSummand (Int.toNat_le.mp hk) z

Depends on / 依赖: Int.toNat_le.mp, summable_norm_eisSummand, summable_norm_iff, summable_norm_iff.mp, toNat_le
-/
lemma summable_eisSummand {k : Nat} (hk : 3 <= k) (z : ℍ) :
    Summable (eisSummand k · z) :=
summable_norm_iff.mp summable_norm_eisSummand (Int.toNat_le.mp hk) z

/--
lemma `summable_prod_eisSummand` / 引理 `summable_prod_eisSummand`

English:
lemma summable_prod_eisSummand
  given: {k : Nat} (hk : 3 <= k) (z : ℍ)
  proof: by
refine (finTwoArrowEquiv Int).summable_iff.mp (summable_eisSummand hk z).congr (fun v => ?_)
  simp [show ![v 0, v 1] = v from List.ofFn_inj.mp rfl]

中文:
引理 summable_prod_eisSummand
  条件: {k : 自然数} (hk : 3 <= k) (z : ℍ)
  证明: by
refine (finTwoArrowEquiv Int).summable_iff.mp (summable_eisSummand hk z).congr (fun v => ?_)
  simp [show ![v 0, v 1] = v from List.ofFn_inj.mp rfl]

Depends on / 依赖: List.ofFn_inj.mp, finTwoArrowEquiv, ofFn_inj, summable_eisSummand, summable_iff, summable_iff.mp
-/
lemma summable_prod_eisSummand {k : Nat} (hk : 3 <= k) (z : ℍ) :
    Summable fun x : Int × Int => eisSummand k ![x.1, x.2] z := by
refine (finTwoArrowEquiv Int).summable_iff.mp (summable_eisSummand hk z).congr (fun v => ?_)
  simp [show ![v 0, v 1] = v from List.ofFn_inj.mp rfl]

/--
lemma `tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow` / 引理 `tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow`

English:
lemma tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow
  given: {k : Nat} (hk : 3 <= k) (hk2 : Even k) (z : ℍ)
  proof: by
  rw [← (finTwoArrowEquiv Int).symm.tsum_eq]; rw [finTwoArrowEquiv_symm_apply]; rw [Summable.tsum_prod (summable_prod_eisSummand hk z)]; rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (fun n => ?h₁)
      (by simpa using (summable_prod_eisSummand hk z).prod)]
  case h₁ =>
    nth_rewrite 1 [← tsum_co

中文:
引理 tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow
  条件: {k : 自然数} (hk : 3 <= k) (hk2 : Even k) (z : ℍ)
  证明: by
  rw [← (finTwoArrowEquiv Int).symm.tsum_eq]; rw [finTwoArrowEquiv_symm_apply]; rw [Summable.tsum_prod (summable_prod_eisSummand hk z)]; rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (fun n => ?h₁)
      (by simpa using (summable_prod_eisSummand hk z).prod)]
  case h₁ =>
    nth_rewrite 1 [← tsum_co

Depends on / 依赖: Summable, Summable.tsum_prod, eisSummand, finTwoArrowEquiv, finTwoArrowEquiv_symm_apply, hk2.neg_pow, neg_add, neg_add_rev, neg_pow, nth_rewrite, qExpansion_identity_pnat, simp_rw, summable_prod_eisSummand, symm.tsum_eq, tsum_comp_neg, tsum_congr, tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat, tsum_prod
-/
lemma tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow {k : Nat} (hk : 3 <= k) (hk2 : Even k) (z : ℍ) :
    ∑' v, eisSummand k v z = 2 * riemannZeta k + 2 * ((-2 * π * I) ^ k / (k - 1)!) *
    ∑' (n : Nat+), σ (k - 1) n * cexp (2 * π * I * z) ^ (n : Nat) := by
  rw [← (finTwoArrowEquiv Int).symm.tsum_eq]; rw [finTwoArrowEquiv_symm_apply]; rw [Summable.tsum_prod (summable_prod_eisSummand hk z)]; rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (fun n => ?h₁)
      (by simpa using (summable_prod_eisSummand hk z).prod)]
  case h₁ =>
    nth_rewrite 1 [← tsum_comp_neg]
    exact tsum_congr fun y => by simp [eisSummand, ← neg_add _ (y : Complex), -neg_add_rev, hk2.neg_pow]
  have H (b : Nat+) := qExpansion_identity_pnat (k := k - 1) (by grind) ⟨b * z, by simpa using z.2⟩
  simp_rw [show k - 1 + 1 = k by grind, one_div] at H
  simp only [neg_mul] at H
  rw [nsmul_eq_mul]; rw [mul_assoc]
  congr
  · simp [eisSummand, two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by grind) hk2]
  · suffices ∑' (m : Nat+) (n : Nat+), (n : Nat) ^ (k - 1) * cexp (2 * π * I * (m * z)) ^ (n : Nat) =
        ∑' (m : Nat+) (n : Nat+), (n : Nat) ^ (k - 1) * cexp (2 * π * I * z) ^ (m * n : Nat) by
      simp [eisSummand, H, tsum_mul_left,
        ← tsum_prod_pow_eq_tsum_sigma (k - 1) (norm_exp_two_pi_I_lt_one z), this]
    simp_rw [← Complex.exp_nat_mul]
    exact tsum_congr₂ (fun m n => by push_cast; ring_nf)

/--
lemma `eisSummand_of_gammaSet_eq_divIntMap` / 引理 `eisSummand_of_gammaSet_eq_divIntMap`

English:
lemma eisSummand_of_gammaSet_eq_divIntMap
  given: (k : Int) (z : ℍ) {n : Nat} (v : gammaSet 1 n 0)
  proof: by
  simp_rw [eisSummand]
  nth_rw 1 2 [gammaSet_eq_gcd_mul_divIntMap v.2]
  simp [← mul_inv, ← mul_zpow, mul_add, mul_assoc]

中文:
引理 eisSummand_of_gammaSet_eq_divIntMap
  条件: (k : 整数) (z : ℍ) {n : 自然数} (v : gammaSet 1 n 0)
  证明: by
  simp_rw [eisSummand]
  nth_rw 1 2 [gammaSet_eq_gcd_mul_divIntMap v.2]
  simp [← mul_inv, ← mul_zpow, mul_add, mul_assoc]

Depends on / 依赖: eisSummand, gammaSet_eq_gcd_mul_divIntMap, mul_add, mul_assoc, mul_inv, mul_zpow, nth_rw, simp_rw
-/
lemma eisSummand_of_gammaSet_eq_divIntMap (k : Int) (z : ℍ) {n : Nat} (v : gammaSet 1 n 0) :
    eisSummand k v z = ((n : Complex) ^ k)⁻¹ * eisSummand k (divIntMap n v) z := by
  simp_rw [eisSummand]
  nth_rw 1 2 [gammaSet_eq_gcd_mul_divIntMap v.2]
  simp [← mul_inv, ← mul_zpow, mul_add, mul_assoc]

/--
lemma `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries` / 引理 `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`

English:
lemma tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries
  given: {k : Nat} (hk : 3 <= k) (z : ℍ)
  proof: by
  have hk1 : 1 < k := by grind
  have hk2 : 3 <= (k : Int) := mod_cast hk
  simp_rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq, gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [eisensteinSeries]; rw [Summable.tsum_sigma ?hsumm]; rw [zeta_nat_eq_tsum_of_gt_one hk1]; rw [tsum_mul_tsum_of_summable_norm (by sim

中文:
引理 tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries
  条件: {k : 自然数} (hk : 3 <= k) (z : ℍ)
  证明: by
  have hk1 : 1 < k := by grind
  have hk2 : 3 <= (k : Int) := mod_cast hk
  simp_rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq, gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [eisensteinSeries]; rw [Summable.tsum_sigma ?hsumm]; rw [zeta_nat_eq_tsum_of_gt_one hk1]; rw [tsum_mul_tsum_of_summable_norm (by sim

Depends on / 依赖: Summable, Summable.tsum_sigma, eisensteinSeries, gammaSetDivGcdSigmaEquiv, gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr, gammaSetDivGcdSigmaEquiv.symm.tsum_eq, gammaSetDivGcdSigmaEquiv_symm_eq, mod_cast, of_norm, one_div, simp_rw, subtype, summable_iff, summable_norm_eisSummand, tsum_eq, tsum_mul_tsum_of_summable_norm, tsum_sigma, zeta_nat_eq_tsum_of_gt_one
-/
lemma tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries {k : Nat} (hk : 3 <= k) (z : ℍ) :
    ∑' v : Fin 2 -> Int, eisSummand k v z = riemannZeta k * eisensteinSeries (N := 1) 0 k z := by
  have hk1 : 1 < k := by grind
  have hk2 : 3 <= (k : Int) := mod_cast hk
  simp_rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq, gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [eisensteinSeries]; rw [Summable.tsum_sigma ?hsumm]; rw [zeta_nat_eq_tsum_of_gt_one hk1]; rw [tsum_mul_tsum_of_summable_norm (by simp [hk1]) ((summable_norm_eisSummand hk2 z).subtype _)]
  case hsumm =>
    exact gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr (summable_norm_eisSummand hk2 z).of_norm
.congr by simp
  simp_rw [one_div]
  rw [Summable.tsum_prod' ?h₁ fun b => ?h₂]
  case h₁ =>
    exact summable_mul_of_summable_norm (f := fun (n : Nat) => ((n : Complex) ^ k)⁻¹)
      (g := fun (v : gammaSet 1 1 0) => eisSummand k v z) (by simp [hk1])
      ((summable_norm_eisSummand hk2 z).subtype _)
  case h₂ =>
    simpa using ((summable_norm_eisSummand hk2 z).subtype _).of_norm.mul_left (a := ((b : Complex) ^ k)⁻¹)
  refine tsum_congr fun b => ?_
  rcases eq_or_ne b 0 with rfl | hb
  · simp [show ((0 : Complex) ^ k)⁻¹ = 0 by aesop, eisSummand_of_gammaSet_eq_divIntMap]
  · have : NeZero b := ⟨hb⟩
    simpa [eisSummand_of_gammaSet_eq_divIntMap k z, tsum_mul_left, hb]
      using (gammaSetDivGcdEquiv b).tsum_eq (eisSummand k · z)

/--
lemma `EisensteinSeries.q_expansion_riemannZeta` / 引理 `EisensteinSeries.q_expansion_riemannZeta`

English:
lemma EisensteinSeries.q_expansion_riemannZeta
  given: {k : Nat} (hk : 3 <= k) (hk2 : Even k) (z : ℍ)
  proof: by
  rw [show E hk z = (1 / 2 : Complex) • eisensteinSeriesSIF (N := 1) 0 k z from rfl]; rw [eisensteinSeriesSIF_apply 0 k z]; rw [eisensteinSeries]
  have HE1 := tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow hk hk2 z
  have HE2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z
have z2 : riem

中文:
引理 EisensteinSeries.q_expansion_riemannZeta
  条件: {k : 自然数} (hk : 3 <= k) (hk2 : Even k) (z : ℍ)
  证明: by
  rw [show E hk z = (1 / 2 : Complex) • eisensteinSeriesSIF (N := 1) 0 k z from rfl]; rw [eisensteinSeriesSIF_apply 0 k z]; rw [eisensteinSeries]
  have HE1 := tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow hk hk2 z
  have HE2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z
have z2 : riem

Depends on / 依赖: eisSummand, eisensteinSeries, eisensteinSeriesSIF, eisensteinSeriesSIF_apply, riemannZeta, riemannZeta_ne_zero_of_one_lt_re, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries, tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow
-/
lemma EisensteinSeries.q_expansion_riemannZeta {k : Nat} (hk : 3 <= k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 + (riemannZeta k)⁻¹ * (-2 * π * I) ^ k / (k - 1)! *
    ∑' n : Nat+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : Int) := by
  rw [show E hk z = (1 / 2 : Complex) • eisensteinSeriesSIF (N := 1) 0 k z from rfl]; rw [eisensteinSeriesSIF_apply 0 k z]; rw [eisensteinSeries]
  have HE1 := tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow hk hk2 z
  have HE2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z
have z2 : riemannZeta k != 0 := riemannZeta_ne_zero_of_one_lt_re by norm_cast; grind
  simp [eisSummand, eisensteinSeries, ← inv_mul_eq_iff_eq_mul₀ z2] at HE1 HE2 ⊢
  grind

/--
lemma `eisensteinSeries_coeff_identity` / 引理 `eisensteinSeries_coeff_identity`

English:
lemma eisensteinSeries_coeff_identity
  given: {k : Nat} (hk2 : Even k) (hkn0 : k != 0)
  proof: by
  have h2 : k = 2 * (k / 2 - 1 + 1) := by grind
  set m := k / 2 - 1
  rw [h2]; rw [Nat.cast_mul 2 (m + 1)]; rw [Nat.cast_two]; rw [riemannZeta_two_mul_nat (show m + 1 != 0 by grind)]; rw [show (2 * (m + 1))! = 2 * (m + 1) * (2 * m + 1)! by grind [Nat.factorial_succ],
    show 2 * (m + 1) - 1 = 2

中文:
引理 eisensteinSeries_coeff_identity
  条件: {k : 自然数} (hk2 : Even k) (hkn0 : k != 0)
  证明: by
  have h2 : k = 2 * (k / 2 - 1 + 1) := by grind
  set m := k / 2 - 1
  rw [h2]; rw [Nat.cast_mul 2 (m + 1)]; rw [Nat.cast_two]; rw [riemannZeta_two_mul_nat (show m + 1 != 0 by grind)]; rw [show (2 * (m + 1))! = 2 * (m + 1) * (2 * m + 1)! by grind [Nat.factorial_succ],
    show 2 * (m + 1) - 1 = 2
-/
private lemma eisensteinSeries_coeff_identity {k : Nat} (hk2 : Even k) (hkn0 : k != 0) :
    (riemannZeta k)⁻¹ * (-2 * π * I) ^ k / (k - 1)! = -(2 * k / bernoulli k) := by
  have h2 : k = 2 * (k / 2 - 1 + 1) := by grind
  set m := k / 2 - 1
  rw [h2]; rw [Nat.cast_mul 2 (m + 1)]; rw [Nat.cast_two]; rw [riemannZeta_two_mul_nat (show m + 1 != 0 by grind)]; rw [show (2 * (m + 1))! = 2 * (m + 1) * (2 * m + 1)! by grind [Nat.factorial_succ],
    show 2 * (m + 1) - 1 = 2 * m + 1 by grind, mul_pow, mul_pow, pow_mul I, I_sq]
  norm_cast
  simp [field]
  grind

/--
lemma `EisensteinSeries.q_expansion_bernoulli` / 引理 `EisensteinSeries.q_expansion_bernoulli`

English:
lemma EisensteinSeries.q_expansion_bernoulli
  given: {k : Nat} (hk : 3 <= k) (hk2 : Even k) (z : ℍ)
  proof: by
  convert! q_expansion_riemannZeta hk hk2 z using 1
  rw [eisensteinSeries_coeff_identity hk2 (by grind)]; rw [neg_mul]; rw [← sub_eq_add_neg]

中文:
引理 EisensteinSeries.q_expansion_bernoulli
  条件: {k : 自然数} (hk : 3 <= k) (hk2 : Even k) (z : ℍ)
  证明: by
  convert! q_expansion_riemannZeta hk hk2 z using 1
  rw [eisensteinSeries_coeff_identity hk2 (by grind)]; rw [neg_mul]; rw [← sub_eq_add_neg]

Depends on / 依赖: convert, eisensteinSeries_coeff_identity, neg_mul, q_expansion_riemannZeta, sub_eq_add_neg
-/
lemma EisensteinSeries.q_expansion_bernoulli {k : Nat} (hk : 3 <= k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 - (2 * k / bernoulli k) *
    ∑' n : Nat+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : Int) := by
  convert! q_expansion_riemannZeta hk hk2 z using 1
  rw [eisensteinSeries_coeff_identity hk2 (by grind)]; rw [neg_mul]; rw [← sub_eq_add_neg]

section NonZero

open ModularFormClass

local notation "𝕢" => Periodic.qParam

/--
lemma `EisensteinSeries.summable_sigma_mul_cexp_pow` / 引理 `EisensteinSeries.summable_sigma_mul_cexp_pow`

English:
lemma EisensteinSeries.summable_sigma_mul_cexp_pow
  given: {k : Nat} (hk : 1 <= k) (z : ℍ)
  proof: by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one k (norm_exp_two_pi_I_lt_one z))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ (k - 1) n).trans_eq (by congr 1; omega)

中文:
引理 EisensteinSeries.summable_sigma_mul_cexp_pow
  条件: {k : 自然数} (hk : 1 <= k) (z : ℍ)
  证明: by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one k (norm_exp_two_pi_I_lt_one z))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ (k - 1) n).trans_eq (by congr 1; omega)

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.sigma_le_pow_succ, Complex.norm_natCast, Summable, Summable.of_norm_bounded, norm_exp_two_pi_I_lt_one, norm_mul, norm_natCast, norm_pow, of_norm_bounded, sigma_le_pow_succ, summable_norm_pow_mul_geometric_of_norm_lt_one, trans_eq
-/
lemma EisensteinSeries.summable_sigma_mul_cexp_pow {k : Nat} (hk : 1 <= k) (z : ℍ) :
    Summable fun n : Nat => (σ (k - 1) n : Complex) * cexp (2 * π * I * z) ^ n := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one k (norm_exp_two_pi_I_lt_one z))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ (k - 1) n).trans_eq (by congr 1; omega)

/--
lemma `EisensteinSeries.E_qExpansion_coeff` / 引理 `EisensteinSeries.E_qExpansion_coeff`

English:
lemma EisensteinSeries.E_qExpansion_coeff
  given: {k : Nat} (hk : 3 <= k) (hk2 : Even k) (m : Nat)
  proof: by
  set β : Complex := -(2 * k / bernoulli k : Complex)
  set c : Nat -> Complex := fun m => if m = 0 then 1 else β * ↑(σ (k - 1) m)
  suffices forall τ : ℍ, HasSum (fun m => c m • 𝕢 (1 : Real) τ ^ m) (E hk τ) from
    (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL this 

中文:
引理 EisensteinSeries.E_qExpansion_coeff
  条件: {k : 自然数} (hk : 3 <= k) (hk2 : Even k) (m : 自然数)
  证明: by
  set β : Complex := -(2 * k / bernoulli k : Complex)
  set c : Nat -> Complex := fun m => if m = 0 then 1 else β * ↑(σ (k - 1) m)
  suffices forall τ : ℍ, HasSum (fun m => c m • 𝕢 (1 : Real) τ ^ m) (E hk τ) from
    (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL this 

Depends on / 依赖: HasSum, ModularFormClass, ModularFormClass.qExpansion_coeff_unique, Summable, bernoulli, hasSum_nat_add_i, one_mem_strictPeriods_SL, one_pos, qExpansion_coeff_unique, summable_nat_add_iff, summable_sigma_mul_cexp_pow
-/
lemma EisensteinSeries.E_qExpansion_coeff {k : Nat} (hk : 3 <= k) (hk2 : Even k) (m : Nat) :
    (qExpansion 1 (E hk)).coeff m =
    if m = 0 then 1 else -(2 * k / bernoulli k : Complex) * (σ (k - 1) m) := by
  set β : Complex := -(2 * k / bernoulli k : Complex)
  set c : Nat -> Complex := fun m => if m = 0 then 1 else β * ↑(σ (k - 1) m)
  suffices forall τ : ℍ, HasSum (fun m => c m • 𝕢 (1 : Real) τ ^ m) (E hk τ) from
    (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL this m).symm
  intro τ
  have hS : Summable fun n : Nat => (σ (k - 1) (n + 1) : Complex) * cexp (2 * π * I * τ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (by omega) τ)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, smul_eq_mul, Finset.range_one,
    ite_mul, one_mul, Finset.sum_singleton, pow_zero, c]
  have hval : E hk τ - 1 = β * ∑' n : Nat, (σ (k - 1) (n + 1)) * cexp (2 * π * I * τ) ^ (n + 1) := by
    have := q_expansion_bernoulli hk hk2 τ
    simp_rw [zpow_natCast] at this
    rw [this]; rw [← tsum_pnat_eq_tsum_succ (f := fun n => (σ (k - 1) n : Complex) * cexp (2 * π * I * τ) ^ n)]
    ring
  rw [hval]
  convert! (hS.mul_left β).hasSum using 1
  · grind [Periodic.qParam, ofReal_one, div_one]
  · rw [tsum_mul_left]

/--
lemma `EisensteinSeries.E_qExpansion_coeff_zero` / 引理 `EisensteinSeries.E_qExpansion_coeff_zero`

English:
lemma EisensteinSeries.E_qExpansion_coeff_zero
  given: {k : Nat} (hk : 3 <= k) (hk2 : Even k)
  proof: by
  simpa using E_qExpansion_coeff hk hk2 0

中文:
引理 EisensteinSeries.E_qExpansion_coeff_zero
  条件: {k : 自然数} (hk : 3 <= k) (hk2 : Even k)
  证明: by
  simpa using E_qExpansion_coeff hk hk2 0

Depends on / 依赖: E_qExpansion_coeff
-/
lemma EisensteinSeries.E_qExpansion_coeff_zero {k : Nat} (hk : 3 <= k) (hk2 : Even k) :
    (qExpansion 1 (E hk)).coeff 0 = 1 := by
  simpa using E_qExpansion_coeff hk hk2 0

/--
theorem `EisensteinSeries.E_ne_zero` / 定理 `EisensteinSeries.E_ne_zero`

English:
theorem EisensteinSeries.E_ne_zero
  given: {k : Nat} (hk : 3 <= k) (hk2 : Even k)
  statement: E hk != 0
  proof: fun h => one_ne_zero (E_qExpansion_coeff_zero hk hk2).symm.trans (by simp [h, qExpansion_zero])

中文:
定理 EisensteinSeries.E_ne_zero
  条件: {k : 自然数} (hk : 3 <= k) (hk2 : Even k)
  结论: E hk != 0
  证明: fun h => one_ne_zero (E_qExpansion_coeff_zero hk hk2).symm.trans (by simp [h, qExpansion_zero])

Depends on / 依赖: E_qExpansion_coeff_zero, one_ne_zero, qExpansion_zero, symm.trans
-/
theorem EisensteinSeries.E_ne_zero {k : Nat} (hk : 3 <= k) (hk2 : Even k) : E hk != 0 :=
fun h => one_ne_zero (E_qExpansion_coeff_zero hk hk2).symm.trans (by simp [h, qExpansion_zero])

end NonZero
