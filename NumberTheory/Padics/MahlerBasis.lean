/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.Binomial
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# The Mahler basis of continuous functions

In this file we introduce the Mahler basis function `mahler k`, for `k : ℕ`, which is the unique
continuous map `ℤ_[p] → ℤ_[p]` agreeing with `n ↦ n.choose k` for `n ∈ ℕ`.

Using this, we prove Mahler's theorem, showing that for any continuous function `f` on `ℤ_[p]`
(valued in a normed `ℤ_[p]`-module `E`), the Mahler series `x ↦ ∑' k, mahler k x • Δ^[n] f 0`
converges (uniformly) to `f`, and this construction defines a Banach-space isomorphism between
`C(ℤ_[p], E)` and the space of sequences `ℕ → E` tending to 0.

For this, we follow the argument of Bojanić [bojanic74].

The formalisation of Mahler's theorem presented here is based on code written by Giulio Caflisch
for his bachelor's thesis at ETH Zürich.

## References

* [R. Bojanić, *A simple proof of Mahler's theorem on approximation of continuous functions of a
  p-adic variable by polynomials*][bojanic74]
* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010]

## Tags

Bojanic
-/

@[expose] public section

open Finset IsUltrametricDist NNReal Filter

open scoped fwdDiff ZeroAtInfty Topology

variable {p : Nat} [hp : Fact p.Prime]

namespace PadicInt

/--
lemma `norm_ascPochhammer_le` / 引理 `norm_ascPochhammer_le`

English:
lemma norm_ascPochhammer_le
  given: (k : Nat) (x : Int_[p])
  proof: by
  let f := (ascPochhammer Int_[p] k).eval
  change ‖f x‖ <= ‖_‖
  have hC : (k.factorial : Int_[p]) != 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hf : ContinuousAt f x := Polynomial.continuousAt _
  -- find `n : ℕ` such that `‖f x - f n‖ ≤ ‖k!‖`
  obtain ⟨n, hn⟩ : exists n : Nat, ‖f x -

中文:
引理 norm_ascPochhammer_le
  条件: (k : 自然数) (x : 整数_[p])
  证明: by
  let f := (ascPochhammer Int_[p] k).eval
  change ‖f x‖ <= ‖_‖
  have hC : (k.factorial : Int_[p]) != 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hf : ContinuousAt f x := Polynomial.continuousAt _
  -- find `n : ℕ` such that `‖f x - f n‖ ≤ ‖k!‖`
  obtain ⟨n, hn⟩ : exists n : Nat, ‖f x -

Depends on / 依赖: ContinuousAt, Int_, Nat.cast_ne_zero.mpr, Polynomial, Polynomial.continuousAt, ascPochhammer, cast_ne_zero, continuousAt, factorial, factorial_ne_zero, k.factorial, k.factorial_ne_zero
-/
lemma norm_ascPochhammer_le (k : Nat) (x : Int_[p]) :
    ‖(ascPochhammer Int_[p] k).eval x‖ <= ‖(k.factorial : Int_[p])‖ := by
  let f := (ascPochhammer Int_[p] k).eval
  change ‖f x‖ <= ‖_‖
  have hC : (k.factorial : Int_[p]) != 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hf : ContinuousAt f x := Polynomial.continuousAt _
  -- find `n : ℕ` such that `‖f x - f n‖ ≤ ‖k!‖`
  obtain ⟨n, hn⟩ : exists n : Nat, ‖f x - f n‖ <= ‖(k.factorial : Int_[p])‖ := by
    obtain ⟨δ, hδp, hδ⟩ := Metric.continuousAt_iff.mp hf _ (norm_pos_iff.mpr hC)
    obtain ⟨n, hn'⟩ := PadicInt.denseRange_natCast.exists_dist_lt x hδp
    simpa only [← dist_eq_norm_sub'] using ⟨n, (hδ (dist_comm x n ▸ hn')).le⟩
  -- use ultrametric property to show that `‖f n‖ ≤ ‖k!‖` implies `‖f x‖ ≤ ‖k!‖`
  refine sub_add_cancel (f x) _ ▸ (IsUltrametricDist.norm_add_le_max _ (f n)).trans (max_le hn ?_)
  -- finish using the fact that `n.multichoose k ∈ ℤ`
  simp_rw [f, ← ascPochhammer_eval_cast, Polynomial.eval_eq_smeval,
    ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer, smul_eq_mul, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddTorsionFree Int_[p]
  body: smul_right_injective Int_[p]

中文:
实例 :
  签名: IsAddTorsionFree 整数_[p]
  定义体: smul_right_injective Int_[p]

Depends on / 依赖: Int_, smul_right_injective
-/
instance : IsAddTorsionFree Int_[p] where
  nsmul_right_injective _ := smul_right_injective Int_[p]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instBinomialRing` / 实例 `instBinomialRing`

English:
instance instBinomialRing
  signature: : BinomialRing Int_[p] where
  body: ⟨(ascPochhammer Int_[p] k).eval x / (k.factorial : Rat_[p]), by
    rw [norm_div]; rw [div_le_one (by simpa using k.factorial_ne_zero)]
    exact x.norm_ascPochhammer_le k⟩
  factorial_nsmul_multichoose x k := by rw [← Subtype.coe_inj, nsmul_eq_mul, PadicInt.coe_mul,
    PadicInt.coe_natCast, mul_di

中文:
实例 instBinomialRing
  签名: : BinomialRing 整数_[p] where
  定义体: ⟨(ascPochhammer Int_[p] k).eval x / (k.factorial : Rat_[p]), by
    rw [norm_div]; rw [div_le_one (by simpa using k.factorial_ne_zero)]
    exact x.norm_ascPochhammer_le k⟩
  factorial_nsmul_multichoose x k := by rw [← Subtype.coe_inj, nsmul_eq_mul, PadicInt.coe_mul,
    PadicInt.coe_natCast, mul_di

Depends on / 依赖: Int_, PadicInt, PadicInt.coe_mul, PadicInt.coe_natCast, Polynomial, Polynomial.ascPochhammer_smeval_cast, Polynomial.eval_eq_smeval, Rat_, Subtype, Subtype.coe_inj, ascPochhammer, ascPochhammer_smeval_cast, coe_inj, coe_mul, coe_natCast, div_le_one, eval_eq_smeval, factorial, factorial_ne_zero, factorial_nsmul_multichoose
-/
noncomputable instance instBinomialRing : BinomialRing Int_[p] where
  -- We define `multichoose` as a fraction in `ℚ_[p]` together with a proof that its norm is `≤ 1`.
  multichoose x k := ⟨(ascPochhammer Int_[p] k).eval x / (k.factorial : Rat_[p]), by
    rw [norm_div]; rw [div_le_one (by simpa using k.factorial_ne_zero)]
    exact x.norm_ascPochhammer_le k⟩
  factorial_nsmul_multichoose x k := by rw [← Subtype.coe_inj, nsmul_eq_mul, PadicInt.coe_mul,
    PadicInt.coe_natCast, mul_div_cancel₀ _ (mod_cast k.factorial_ne_zero), Subtype.coe_inj,
    Polynomial.eval_eq_smeval, Polynomial.ascPochhammer_smeval_cast]

@[fun_prop]
/--
lemma `continuous_multichoose` / 引理 `continuous_multichoose`

English:
lemma continuous_multichoose
  given: (k : Nat)
  statement: Continuous (fun x : Int_[p] => Ring.multichoose x k)
  proof: by
  simp only [Ring.multichoose, BinomialRing.multichoose]
  fun_prop

@[fun_prop]

中文:
引理 continuous_multichoose
  条件: (k : 自然数)
  结论: Continuous (fun x : 整数_[p] => Ring.multichoose x k)
  证明: by
  simp only [Ring.multichoose, BinomialRing.multichoose]
  fun_prop

@[fun_prop]

Depends on / 依赖: BinomialRing, BinomialRing.multichoose, Ring.multichoose, fun_prop, multichoose
-/
lemma continuous_multichoose (k : Nat) : Continuous (fun x : Int_[p] => Ring.multichoose x k) := by
  simp only [Ring.multichoose, BinomialRing.multichoose]
  fun_prop

@[fun_prop]
/--
lemma `continuous_choose` / 引理 `continuous_choose`

English:
lemma continuous_choose
  given: (k : Nat)
  statement: Continuous (fun x : Int_[p] => Ring.choose x k)
  proof: by
  simp only [Ring.choose]
  fun_prop

中文:
引理 continuous_choose
  条件: (k : 自然数)
  结论: Continuous (fun x : 整数_[p] => Ring.choose x k)
  证明: by
  simp only [Ring.choose]
  fun_prop

Depends on / 依赖: Ring.choose, fun_prop
-/
lemma continuous_choose (k : Nat) : Continuous (fun x : Int_[p] => Ring.choose x k) := by
  simp only [Ring.choose]
  fun_prop

end PadicInt

/--
Definition of `mahler` / `mahler` 的定义

English:
definition mahler
  signature: (k : Nat)
  body: Ring.choose x k
  continuous_toFun := PadicInt.continuous_choose k

中文:
定义 mahler
  签名: (k : 自然数)
  定义体: Ring.choose x k
  continuous_toFun := PadicInt.continuous_choose k

Depends on / 依赖: Ring.choose
-/
noncomputable def mahler (k : Nat) : C(Int_[p], Int_[p]) where
  toFun x := Ring.choose x k
  continuous_toFun := PadicInt.continuous_choose k

/--
lemma `mahler_apply` / 引理 `mahler_apply`

English:
lemma mahler_apply
  given: (k : Nat) (x : Int_[p])
  statement: mahler k x = Ring.choose x k
  proof: rfl

中文:
引理 mahler_apply
  条件: (k : 自然数) (x : 整数_[p])
  结论: mahler k x = Ring.choose x k
  证明: rfl
-/
lemma mahler_apply (k : Nat) (x : Int_[p]) : mahler k x = Ring.choose x k := rfl

/--
lemma `mahler_natCast_eq` / 引理 `mahler_natCast_eq`

English:
lemma mahler_natCast_eq
  given: (k n : Nat)
  statement: mahler k (n : Int_[p]) = n.choose k
  proof: by
  simp only [mahler_apply, Ring.choose_natCast]

中文:
引理 mahler_natCast_eq
  条件: (k n : 自然数)
  结论: mahler k (n : 整数_[p]) = n.choose k
  证明: by
  simp only [mahler_apply, Ring.choose_natCast]

Depends on / 依赖: Ring.choose_natCast, choose_natCast, mahler_apply
-/
lemma mahler_natCast_eq (k n : Nat) : mahler k (n : Int_[p]) = n.choose k := by
  simp only [mahler_apply, Ring.choose_natCast]

section fwdDiff

variable {M G : Type*}

/--
lemma `IsUltrametricDist.norm_fwdDiff_iter_apply_le` / 引理 `IsUltrametricDist.norm_fwdDiff_iter_apply_le`

English:
lemma IsUltrametricDist.norm_fwdDiff_iter_apply_le
  statement: [TopologicalSpace M] [CompactSpace M]
  proof: by
  -- A proof by induction on `n` would be possible but would involve some messing around to
  -- define `Δ_[h]` as an operator on continuous maps (not just on bare functions). So instead we
  -- use the formula for `Δ_[h]^[n] f` as a sum.
  rw [fwdDiff_iter_eq_sum_shift]
  refine norm_sum_le_of_f

中文:
引理 IsUltrametricDist.norm_fwdDiff_iter_apply_le
  结论: [TopologicalSpace M] [CompactSpace M]
  证明: by
  -- A proof by induction on `n` would be possible but would involve some messing around to
  -- define `Δ_[h]` as an operator on continuous maps (not just on bare functions). So instead we
  -- use the formula for `Δ_[h]^[n] f` as a sum.
  rw [fwdDiff_iter_eq_sum_shift]
  refine norm_sum_le_of_f
-/
lemma IsUltrametricDist.norm_fwdDiff_iter_apply_le [TopologicalSpace M] [CompactSpace M]
    [AddCommMonoid M] [SeminormedAddCommGroup G] [IsUltrametricDist G]
    (h : M) (f : C(M, G)) (m : M) (n : Nat) : ‖Δ_[h]^[n] f m‖ <= ‖f‖ := by
  -- A proof by induction on `n` would be possible but would involve some messing around to
  -- define `Δ_[h]` as an operator on continuous maps (not just on bare functions). So instead we
  -- use the formula for `Δ_[h]^[n] f` as a sum.
  rw [fwdDiff_iter_eq_sum_shift]
  refine norm_sum_le_of_forall_le_of_nonneg (norm_nonneg f) fun i _ => ?_
  exact (norm_zsmul_le _ _).trans (f.norm_coe_le_norm _)

/--
lemma `bojanic_mahler_step1` / 引理 `bojanic_mahler_step1`

English:
lemma bojanic_mahler_step1
  statement: [AddCommMonoidWithOne M] [AddCommGroup G] (f : M -> G)
  proof: by
  have aux : Δ_[1]^[n + R] f 0 = R.choose (R - 1 + 1) • Δ_[1]^[n + R] f 0 := by
    rw [Nat.sub_add_cancel hR]; rw [Nat.choose_self]; rw [one_smul]
  rw [neg_add_eq_sub]; rw [eq_sub_iff_add_eq]; rw [add_comm]; rw [aux]; rw [(by lia : n + R = (n + ((R - 1) + 1)))]; rw [← sum_range_succ]; rw [Nat.s

中文:
引理 bojanic_mahler_step1
  结论: [AddCommMonoidWithOne M] [AddCommGroup G] (f : M -> G)
  证明: by
  have aux : Δ_[1]^[n + R] f 0 = R.choose (R - 1 + 1) • Δ_[1]^[n + R] f 0 := by
    rw [Nat.sub_add_cancel hR]; rw [Nat.choose_self]; rw [one_smul]
  rw [neg_add_eq_sub]; rw [eq_sub_iff_add_eq]; rw [add_comm]; rw [aux]; rw [(by lia : n + R = (n + ((R - 1) + 1)))]; rw [← sum_range_succ]; rw [Nat.s
-/
private lemma bojanic_mahler_step1 [AddCommMonoidWithOne M] [AddCommGroup G] (f : M -> G)
    (n : Nat) {R : Nat} (hR : 1 <= R) :
    Δ_[1]^[n + R] f 0 = -∑ j in range (R - 1), R.choose (j + 1) • Δ_[1]^[n + (j + 1)] f 0 +
      ∑ k in range (n + 1), ((-1 : Int) ^ (n - k) * n.choose k) • (f (k + R) - f k) := by
  have aux : Δ_[1]^[n + R] f 0 = R.choose (R - 1 + 1) • Δ_[1]^[n + R] f 0 := by
    rw [Nat.sub_add_cancel hR]; rw [Nat.choose_self]; rw [one_smul]
  rw [neg_add_eq_sub]; rw [eq_sub_iff_add_eq]; rw [add_comm]; rw [aux]; rw [(by lia : n + R = (n + ((R - 1) + 1)))]; rw [← sum_range_succ]; rw [Nat.sub_add_cancel hR]; rw [← sub_eq_iff_eq_add.mpr (sum_range_succ' (fun x => R.choose x • Δ_[1]^[n + x] f 0) R), add_zero,
    Nat.choose_zero_right, one_smul]
  have : ∑ k in Finset.range (R + 1), R.choose k • Δ_[1]^[n + k] f 0 = Δ_[1]^[n] f R := by
    simpa only [← Function.iterate_add_apply, add_comm, nsmul_one, add_zero] using
      (shift_eq_sum_fwdDiff_iter 1 (Δ_[1]^[n] f) R 0).symm
  simp only [this, fwdDiff_iter_eq_sum_shift (1 : M) f n, mul_comm, nsmul_one, mul_smul, add_comm,
    add_zero, smul_sub, sum_sub_distrib]

end fwdDiff

namespace PadicInt

section norm_fwdDiff

variable {p : Nat} [hp : Fact p.Prime] {E : Type*}
  [NormedAddCommGroup E] [Module Int_[p] E] [IsBoundedSMul Int_[p] E] [IsUltrametricDist E]

/--
lemma `bojanic_mahler_step2` / 引理 `bojanic_mahler_step2`

English:
lemma bojanic_mahler_step2
  statement: {f : C(Int_[p], E)} {s t : Nat}
  proof: by
  -- Use previous lemma to rewrite in a convenient form.
  rw [bojanic_mahler_step1 _ _ (one_le_pow₀ hp.out.one_le)]
  -- Now use ultrametric property and bound each term separately.
  refine (norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · -- Bounding the sum over `range (p ^ t - 1)`: every te

中文:
引理 bojanic_mahler_step2
  结论: {f : C(整数_[p], E)} {s t : 自然数}
  证明: by
  -- Use previous lemma to rewrite in a convenient form.
  rw [bojanic_mahler_step1 _ _ (one_le_pow₀ hp.out.one_le)]
  -- Now use ultrametric property and bound each term separately.
  refine (norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · -- Bounding the sum over `range (p ^ t - 1)`: every te
-/
private lemma bojanic_mahler_step2 {f : C(Int_[p], E)} {s t : Nat}
    (hst : forall x y : Int_[p], ‖x - y‖ <= p ^ (-t : Int) -> ‖f x - f y‖ <= ‖f‖ / p ^ s) (n : Nat) :
    ‖Δ_[1]^[n + p ^ t] f 0‖ <= max ↑((Finset.range (p ^ t - 1)).sup
      fun j => ‖Δ_[1]^[n + (j + 1)] f 0‖₊ / p) (‖f‖ / p ^ s) := by
  -- Use previous lemma to rewrite in a convenient form.
  rw [bojanic_mahler_step1 _ _ (one_le_pow₀ hp.out.one_le)]
  -- Now use ultrametric property and bound each term separately.
  refine (norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · -- Bounding the sum over `range (p ^ t - 1)`: every term involves a value `Δ_[1]^[·] f 0` and
    -- a binomial coefficient which is divisible by `p`
    rw [norm_neg]; rw [← coe_nnnorm]; rw [coe_le_coe]
    refine nnnorm_sum_le_of_forall_le (fun i hi => Finset.le_sup_of_le hi ?_)
    rw [← Nat.cast_smul_eq_nsmul Int_[p], div_eq_inv_mul]
refine (nnnorm_smul_le _ _).trans mul_le_mul_of_nonneg_right ?_ (by simp only [zero_le])
    -- remains to show norm of binomial coeff is `≤ p⁻¹`
    rw [mem_range] at hi
    have : 0 < (p ^ t).choose (i + 1) := Nat.choose_pos (by omega)
    rw [← zpow_neg_one]; rw [← coe_le_coe]; rw [coe_nnnorm]; rw [PadicInt.norm_eq_zpow_neg_valuation
      (mod_cast this.ne')]; rw [coe_zpow]; rw [NNReal.coe_natCast]; rw [zpow_le_zpow_iff_right₀ (mod_cast hp.out.one_lt)]; rw [neg_le_neg_iff]; rw [← PadicInt.valuation_coe]; rw [PadicInt.coe_natCast]; rw [Padic.valuation_natCast]; rw [Nat.one_le_cast]
exact one_le_padicValNat_of_dvd this.ne' hp.out.dvd_choose_pow (by lia) (by omega)
  · -- Bounding the sum over `range (n + 1)`: every term is small by the choice of `t`
    refine norm_sum_le_of_forall_le_of_nonempty nonempty_range_add_one (fun i _ => ?_)
    calc ‖((-1 : Int) ^ (n - i) * n.choose i) • (f (i + ↑(p ^ t)) - f i)‖
    _ <= ‖((-1 : Int) ^ (n - i) * n.choose i : Int_[p])‖ * ‖(f (i + ↑(p ^ t)) - f i)‖ := by
      rw [← Int.cast_smul_eq_zsmul Int_[p]]
      exact (norm_smul_le ..).trans (by norm_cast)
    _ <= ‖f (i + ↑(p ^ t)) - f i‖ := by
      apply mul_le_of_le_one_left (norm_nonneg _)
      simpa only [← coe_intCast] using norm_le_one _
    _ <= ‖f‖ / p ^ s := by
      apply hst
      rw [Nat.cast_pow]; rw [add_sub_cancel_left]; rw [norm_pow]; rw [norm_p]; rw [inv_pow]; rw [zpow_neg]; rw [zpow_natCast]

/--
lemma `fwdDiff_iter_le_of_forall_le` / 引理 `fwdDiff_iter_le_of_forall_le`

English:
lemma fwdDiff_iter_le_of_forall_le
  statement: {f : C(Int_[p], E)} {s t : Nat}
  proof: by
  -- We show the following more general statement by induction on `k`:
  suffices forall {k : Nat}, k <= s -> ‖Δ_[1]^[n + k * p ^ t] f 0‖ <= ‖f‖ / p ^ k from this le_rfl
  intro k hk
  induction k generalizing n with
  | zero => -- base case just says that `‖Δ^[·] (⇑f) 0‖` is bounded by `‖f‖`
   

中文:
引理 fwdDiff_iter_le_of_forall_le
  结论: {f : C(整数_[p], E)} {s t : 自然数}
  证明: by
  -- We show the following more general statement by induction on `k`:
  suffices forall {k : Nat}, k <= s -> ‖Δ_[1]^[n + k * p ^ t] f 0‖ <= ‖f‖ / p ^ k from this le_rfl
  intro k hk
  induction k generalizing n with
  | zero => -- base case just says that `‖Δ^[·] (⇑f) 0‖` is bounded by `‖f‖`
   
-/
lemma fwdDiff_iter_le_of_forall_le {f : C(Int_[p], E)} {s t : Nat}
    (hst : forall x y : Int_[p], ‖x - y‖ <= p ^ (-t : Int) -> ‖f x - f y‖ <= ‖f‖ / p ^ s) (n : Nat) :
    ‖Δ_[1]^[n + s * p ^ t] f 0‖ <= ‖f‖ / p ^ s := by
  -- We show the following more general statement by induction on `k`:
  suffices forall {k : Nat}, k <= s -> ‖Δ_[1]^[n + k * p ^ t] f 0‖ <= ‖f‖ / p ^ k from this le_rfl
  intro k hk
  induction k generalizing n with
  | zero => -- base case just says that `‖Δ^[·] (⇑f) 0‖` is bounded by `‖f‖`
    simpa only [zero_mul, pow_zero, add_zero, div_one] using norm_fwdDiff_iter_apply_le 1 f 0 n
  | succ k IH => -- induction is the "step 2" lemma above
    rw [add_mul]; rw [one_mul]; rw [← add_assoc]
    refine (bojanic_mahler_step2 hst (n + k * p ^ t)).trans (max_le ?_ ?_)
    · rw [← coe_nnnorm, ← NNReal.coe_natCast, ← NNReal.coe_pow, ← NNReal.coe_div, NNReal.coe_le_coe]
      refine Finset.sup_le fun j _ => ?_
      rw [pow_succ]; rw [← div_div]; rw [div_le_div_iff_of_pos_right (mod_cast hp.out.pos)]; rw [add_right_comm]
      exact_mod_cast IH (n + (j + 1)) (by lia)
    · exact div_le_div_of_nonneg_left (norm_nonneg _)
        (mod_cast pow_pos hp.out.pos _) (mod_cast pow_le_pow_right₀ hp.out.one_le hk)

/--
lemma `fwdDiff_tendsto_zero` / 引理 `fwdDiff_tendsto_zero`

English:
lemma fwdDiff_tendsto_zero
  given: (f : C(Int_[p], E))
  statement: Tendsto (Δ_[1]^[·] f 0) atTop (𝓝 0)
  proof: by
  -- first extract an `s`
  refine NormedAddGroup.tendsto_nhds_zero.mpr (fun ε hε => ?_)
  have : Tendsto (fun s => ‖f‖ / p ^ s) _ _ := tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (mod_cast hp.out.one_lt))
  obtain ⟨s, hs⟩ := (this.eventually_lt_const hε).exists
  refine .

中文:
引理 fwdDiff_tendsto_zero
  条件: (f : C(整数_[p], E))
  结论: Tendsto (Δ_[1]^[·] f 0) atTop (𝓝 0)
  证明: by
  -- first extract an `s`
  refine NormedAddGroup.tendsto_nhds_zero.mpr (fun ε hε => ?_)
  have : Tendsto (fun s => ‖f‖ / p ^ s) _ _ := tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (mod_cast hp.out.one_lt))
  obtain ⟨s, hs⟩ := (this.eventually_lt_const hε).exists
  refine .
-/
lemma fwdDiff_tendsto_zero (f : C(Int_[p], E)) : Tendsto (Δ_[1]^[·] f 0) atTop (𝓝 0) := by
  -- first extract an `s`
  refine NormedAddGroup.tendsto_nhds_zero.mpr (fun ε hε => ?_)
  have : Tendsto (fun s => ‖f‖ / p ^ s) _ _ := tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (mod_cast hp.out.one_lt))
  obtain ⟨s, hs⟩ := (this.eventually_lt_const hε).exists
  refine .mp ?_ (.of_forall fun x hx => lt_of_le_of_lt hx hs)
  -- use uniform continuity to find `t`
  obtain ⟨t, ht⟩ : exists t : Nat, forall x y, ‖x - y‖ <= p ^ (-t : Int) -> ‖f x - f y‖ <= ‖f‖ / p ^ s := by
    rcases eq_or_ne f 0 with rfl | hf
    · -- silly case : f = 0
      simp
    have : 0 < ‖f‖ / p ^ s := div_pos (norm_pos_iff.mpr hf) (mod_cast pow_pos hp.out.pos _)
    obtain ⟨δ, hδpos, hδf⟩ := f.uniform_continuity _ this
    obtain ⟨t, ht⟩ := PadicInt.exists_pow_neg_lt p hδpos
    exact ⟨t, fun x y hxy => by simpa only [dist_eq_norm_sub] using (hδf (hxy.trans_lt ht)).le⟩
  filter_upwards [eventually_ge_atTop (s * p ^ t)] with m hm
  simpa only [Nat.sub_add_cancel hm] using fwdDiff_iter_le_of_forall_le ht (m - s * p ^ t)

end norm_fwdDiff

section mahler_coeff

variable {E : Type*} [NormedAddCommGroup E] [Module Int_[p] E] [IsBoundedSMul Int_[p] E]
  (a : E) (n : Nat) (x : Int_[p])

/--
Definition of `mahlerTerm` / `mahlerTerm` 的定义

English:
definition mahlerTerm
  signature: : C(Int_[p], E)
  body: (mahler n : C(_, Int_[p])) • .const _ a

中文:
定义 mahlerTerm
  签名: : C(整数_[p], E)
  定义体: (mahler n : C(_, Int_[p])) • .const _ a

Depends on / 依赖: Int_, mahler
-/
noncomputable def mahlerTerm : C(Int_[p], E) := (mahler n : C(_, Int_[p])) • .const _ a

/--
lemma `mahlerTerm_apply` / 引理 `mahlerTerm_apply`

English:
lemma mahlerTerm_apply
  statement: mahlerTerm a n x = mahler n x • a
  proof: by
  simp only [mahlerTerm, ContinuousMap.smul_apply', ContinuousMap.const_apply]

@[simp]

中文:
引理 mahlerTerm_apply
  结论: mahlerTerm a n x = mahler n x • a
  证明: by
  simp only [mahlerTerm, ContinuousMap.smul_apply', ContinuousMap.const_apply]

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.const_apply, ContinuousMap.smul_apply, const_apply, mahlerTerm, smul_apply
-/
lemma mahlerTerm_apply : mahlerTerm a n x = mahler n x • a := by
  simp only [mahlerTerm, ContinuousMap.smul_apply', ContinuousMap.const_apply]

@[simp]
/--
lemma `norm_mahlerTerm` / 引理 `norm_mahlerTerm`

English:
lemma norm_mahlerTerm
  statement: ‖(mahlerTerm a n : C(Int_[p], E))‖ = ‖a‖
  proof: by
  apply le_antisymm
  · -- Show all values have norm ≤ 1
    rw [ContinuousMap.norm_le_of_nonempty]
refine fun _ => (norm_smul_le _ _).trans mul_le_of_le_one_left (norm_nonneg _) (norm_le_one _)
  · -- Show norm 1 is attained at `x = k`
refine le_trans ?_ (mahlerTerm a n).norm_coe_le_norm n
    s

中文:
引理 norm_mahlerTerm
  结论: ‖(mahlerTerm a n : C(整数_[p], E))‖ = ‖a‖
  证明: by
  apply le_antisymm
  · -- Show all values have norm ≤ 1
    rw [ContinuousMap.norm_le_of_nonempty]
refine fun _ => (norm_smul_le _ _).trans mul_le_of_le_one_left (norm_nonneg _) (norm_le_one _)
  · -- Show norm 1 is attained at `x = k`
refine le_trans ?_ (mahlerTerm a n).norm_coe_le_norm n
    s

Depends on / 依赖: ContinuousMap, ContinuousMap.norm_le_of_nonempty, attained, le_antisymm, le_trans, mahlerTerm, mahlerTerm_apply, mahler_natCast_eq, mul_le_of_le_one_left, norm_coe_le_norm, norm_le_of_nonempty, norm_le_one, norm_nonneg, norm_smul_le, values
-/
lemma norm_mahlerTerm : ‖(mahlerTerm a n : C(Int_[p], E))‖ = ‖a‖ := by
  apply le_antisymm
  · -- Show all values have norm ≤ 1
    rw [ContinuousMap.norm_le_of_nonempty]
refine fun _ => (norm_smul_le _ _).trans mul_le_of_le_one_left (norm_nonneg _) (norm_le_one _)
  · -- Show norm 1 is attained at `x = k`
refine le_trans ?_ (mahlerTerm a n).norm_coe_le_norm n
    simp [mahlerTerm_apply, mahler_natCast_eq]

@[simp]
/--
lemma `mahlerTerm_one` / 引理 `mahlerTerm_one`

English:
lemma mahlerTerm_one
  statement: (mahlerTerm 1 n : C(Int_[p], Int_[p])) = mahler n
  proof: by
  ext; simp [mahlerTerm_apply]

中文:
引理 mahlerTerm_one
  结论: (mahlerTerm 1 n : C(整数_[p], 整数_[p])) = mahler n
  证明: by
  ext; simp [mahlerTerm_apply]

Depends on / 依赖: mahlerTerm_apply
-/
lemma mahlerTerm_one : (mahlerTerm 1 n : C(Int_[p], Int_[p])) = mahler n := by
  ext; simp [mahlerTerm_apply]

/--
lemma `norm_mahler_eq` / 引理 `norm_mahler_eq`

English:
lemma norm_mahler_eq
  given: (k : Nat)
  statement: ‖(mahler k : C(Int_[p], Int_[p]))‖ = 1
  proof: by
  simp [← mahlerTerm_one]

中文:
引理 norm_mahler_eq
  条件: (k : 自然数)
  结论: ‖(mahler k : C(整数_[p], 整数_[p]))‖ = 1
  证明: by
  simp [← mahlerTerm_one]
-/
@[simp] lemma norm_mahler_eq (k : Nat) : ‖(mahler k : C(Int_[p], Int_[p]))‖ = 1 := by
  simp [← mahlerTerm_one]

/--
Definition of `mahlerSeries` / `mahlerSeries` 的定义

English:
definition mahlerSeries
  signature: (a : Nat -> E)
  body: ∑' n, mahlerTerm (a n) n

中文:
定义 mahlerSeries
  签名: (a : 自然数 -> E)
  定义体: ∑' n, mahlerTerm (a n) n

Depends on / 依赖: mahlerTerm
-/
noncomputable def mahlerSeries (a : Nat -> E) : C(Int_[p], E) := ∑' n, mahlerTerm (a n) n

variable [IsUltrametricDist E] [CompleteSpace E] {a : Nat -> E}

/--
lemma `hasSum_mahlerSeries` / 引理 `hasSum_mahlerSeries`

English:
lemma hasSum_mahlerSeries
  given: (ha : Tendsto a atTop (𝓝 0))
  proof: by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  rw [tendsto_zero_iff_norm_tendsto_zero] at ha ⊢
  simpa only [norm_mahlerTerm, Nat.cofinite_eq_atTop] using ha

中文:
引理 hasSum_mahlerSeries
  条件: (ha : Tendsto a atTop (𝓝 0))
  证明: by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  rw [tendsto_zero_iff_norm_tendsto_zero] at ha ⊢
  simpa only [norm_mahlerTerm, Nat.cofinite_eq_atTop] using ha

Depends on / 依赖: Nat.cofinite_eq_atTop, NonarchimedeanAddGroup, NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero, cofinite_eq_atTop, hasSum, norm_mahlerTerm, summable_of_tendsto_cofinite_zero, tendsto_zero_iff_norm_tendsto_zero
-/
lemma hasSum_mahlerSeries (ha : Tendsto a atTop (𝓝 0)) :
    HasSum (fun n => mahlerTerm (a n) n) (mahlerSeries a : C(Int_[p], E)) := by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  rw [tendsto_zero_iff_norm_tendsto_zero] at ha ⊢
  simpa only [norm_mahlerTerm, Nat.cofinite_eq_atTop] using ha

/--
lemma `mahlerSeries_apply` / 引理 `mahlerSeries_apply`

English:
lemma mahlerSeries_apply
  given: (ha : Tendsto a atTop (𝓝 0)) (x : Int_[p])
  proof: by
  simp only [mahlerSeries, ← ContinuousMap.tsum_apply (hasSum_mahlerSeries ha).summable,
    mahlerTerm_apply]

中文:
引理 mahlerSeries_apply
  条件: (ha : Tendsto a atTop (𝓝 0)) (x : 整数_[p])
  证明: by
  simp only [mahlerSeries, ← ContinuousMap.tsum_apply (hasSum_mahlerSeries ha).summable,
    mahlerTerm_apply]

Depends on / 依赖: ContinuousMap, ContinuousMap.tsum_apply, hasSum_mahlerSeries, mahlerSeries, mahlerTerm_apply, summable, tsum_apply
-/
lemma mahlerSeries_apply (ha : Tendsto a atTop (𝓝 0)) (x : Int_[p]) :
    mahlerSeries a x = ∑' n, mahler n x • a n := by
  simp only [mahlerSeries, ← ContinuousMap.tsum_apply (hasSum_mahlerSeries ha).summable,
    mahlerTerm_apply]

/--
lemma `mahlerSeries_apply_nat` / 引理 `mahlerSeries_apply_nat`

English:
lemma mahlerSeries_apply_nat
  given: (ha : Tendsto a atTop (𝓝 0)) {m n : Nat} (hmn : m <= n)
  proof: by
  have h_van (i) : m.choose (i + (n + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  have aux : Summable fun i => m.choose (i + (n + 1)) • a (i + (n + 1)) := by
    simpa only [h_van, zero_smul] using summable_zero
  simp only [mahlerSeries_apply ha, mahler_natCast_eq, Nat.cast_smul_eq_nsmul, add

中文:
引理 mahlerSeries_apply_nat
  条件: (ha : Tendsto a atTop (𝓝 0)) {m n : 自然数} (hmn : m <= n)
  证明: by
  have h_van (i) : m.choose (i + (n + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  have aux : Summable fun i => m.choose (i + (n + 1)) • a (i + (n + 1)) := by
    simpa only [h_van, zero_smul] using summable_zero
  simp only [mahlerSeries_apply ha, mahler_natCast_eq, Nat.cast_smul_eq_nsmul, add

Depends on / 依赖: Nat.cast_smul_eq_nsmul, Nat.choose_eq_zero_of_lt, Summable, add_zero, aux.sum_add_tsum_nat_add, cast_smul_eq_nsmul, choose_eq_zero_of_lt, h_van, m.choose, mahlerSeries_apply, mahler_natCast_eq, sum_add_tsum_nat_add, summable_zero, tsum_zero, zero_smul
-/
lemma mahlerSeries_apply_nat (ha : Tendsto a atTop (𝓝 0)) {m n : Nat} (hmn : m <= n) :
    mahlerSeries a (m : Int_[p]) = ∑ i in range (n + 1), m.choose i • a i := by
  have h_van (i) : m.choose (i + (n + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  have aux : Summable fun i => m.choose (i + (n + 1)) • a (i + (n + 1)) := by
    simpa only [h_van, zero_smul] using summable_zero
  simp only [mahlerSeries_apply ha, mahler_natCast_eq, Nat.cast_smul_eq_nsmul, add_zero,
    ← aux.sum_add_tsum_nat_add' (f := fun i => m.choose i • a i), h_van, zero_smul, tsum_zero]

/--
lemma `fwdDiff_mahlerSeries` / 引理 `fwdDiff_mahlerSeries`

English:
lemma fwdDiff_mahlerSeries
  given: (ha : Tendsto a atTop (𝓝 0)) (n)
  proof: calc Δ_[1]^[n] (mahlerSeries a) 0
  -- throw away terms after the nth
  _ = Δ_[1]^[n] (fun k => ∑ j in range (n + 1), k.choose j • (a j)) 0 := by
    simp only [fwdDiff_iter_eq_sum_shift, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [nsmul_one]; rw [nsmul_one]; rw [mahlerSeries_ap

中文:
引理 fwdDiff_mahlerSeries
  条件: (ha : Tendsto a atTop (𝓝 0)) (n)
  证明: calc Δ_[1]^[n] (mahlerSeries a) 0
  -- throw away terms after the nth
  _ = Δ_[1]^[n] (fun k => ∑ j in range (n + 1), k.choose j • (a j)) 0 := by
    simp only [fwdDiff_iter_eq_sum_shift, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [nsmul_one]; rw [nsmul_one]; rw [mahlerSeries_ap

Depends on / 依赖: mahlerSeries
-/
lemma fwdDiff_mahlerSeries (ha : Tendsto a atTop (𝓝 0)) (n) :
    Δ_[1]^[n] (mahlerSeries a) (0 : Int_[p]) = a n :=
  calc Δ_[1]^[n] (mahlerSeries a) 0
  -- throw away terms after the nth
  _ = Δ_[1]^[n] (fun k => ∑ j in range (n + 1), k.choose j • (a j)) 0 := by
    simp only [fwdDiff_iter_eq_sum_shift, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [nsmul_one]; rw [nsmul_one]; rw [mahlerSeries_apply_nat ha (Nat.lt_succ_iff.mp <| Finset.mem_range.mp hj)]; rw [Nat.cast_id]
  -- bring `Δ_[1]` inside sum
  _ = ∑ j in range (n + 1), Δ_[1]^[n] (fun k => k.choose j • (a j)) 0 := by
    simp only [fwdDiff_iter_eq_sum_shift, smul_sum]
    rw [sum_comm]
  -- bring `Δ_[1]` inside scalar-mult
  _ = ∑ j in range (n + 1), (Δ_[1]^[n] (fun k => k.choose j : Nat -> Int) 0) • (a j) := by
    simp only [fwdDiff_iter_eq_sum_shift, zero_add, sum_smul, smul_assoc,
      natCast_zsmul]
  -- finish using `fwdDiff_iter_choose_zero`
  _ = a n := by
    simp only [fwdDiff_iter_choose_zero, ite_smul, one_smul, zero_smul, sum_ite_eq,
      Finset.mem_range, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte]

/--
lemma `hasSum_mahler` / 引理 `hasSum_mahler`

English:
lemma hasSum_mahler
  given: (f : C(Int_[p], E))
  statement: HasSum (fun n => mahlerTerm (Δ_[1]^[n] f 0) n) f
  proof: by
  -- First show `∑' n, mahlerTerm f n` converges to *something*.
  have : HasSum (fun n => mahlerTerm (Δ_[1]^[n] f 0) n)
      (mahlerSeries (Δ_[1]^[·] f 0) : C(Int_[p], E)) :=
    hasSum_mahlerSeries (fwdDiff_tendsto_zero f)
  -- Now show that the sum of the Mahler terms must equal `f` on a dens

中文:
引理 hasSum_mahler
  条件: (f : C(整数_[p], E))
  结论: HasSum (fun n => mahlerTerm (Δ_[1]^[n] f 0) n) f
  证明: by
  -- First show `∑' n, mahlerTerm f n` converges to *something*.
  have : HasSum (fun n => mahlerTerm (Δ_[1]^[n] f 0) n)
      (mahlerSeries (Δ_[1]^[·] f 0) : C(Int_[p], E)) :=
    hasSum_mahlerSeries (fwdDiff_tendsto_zero f)
  -- Now show that the sum of the Mahler terms must equal `f` on a dens
-/
lemma hasSum_mahler (f : C(Int_[p], E)) : HasSum (fun n => mahlerTerm (Δ_[1]^[n] f 0) n) f := by
  -- First show `∑' n, mahlerTerm f n` converges to *something*.
  have : HasSum (fun n => mahlerTerm (Δ_[1]^[n] f 0) n)
      (mahlerSeries (Δ_[1]^[·] f 0) : C(Int_[p], E)) :=
    hasSum_mahlerSeries (fwdDiff_tendsto_zero f)
  -- Now show that the sum of the Mahler terms must equal `f` on a dense set, so it is actually `f`.
  convert! this using 1
  refine ContinuousMap.coe_injective (denseRange_natCast.equalizer
    (map_continuous f) (map_continuous _) (funext fun n => ?_))
  simpa [mahlerSeries_apply_nat (fwdDiff_tendsto_zero f) le_rfl]
    using shift_eq_sum_fwdDiff_iter 1 f n 0

set_option backward.isDefEq.respectTransparency false in
variable (E) in
/--
Definition of `mahlerEquiv` / `mahlerEquiv` 的定义

English:
definition mahlerEquiv
  signature: : C(Int_[p], E) ≃ₗᵢ[Int_[p]] C₀(Nat, E) where
  body: ⟨⟨(Δ_[1]^[·] f 0), continuous_of_discreteTopology⟩,
    cocompact_eq_atTop (α := Nat) ▸ fwdDiff_tendsto_zero f⟩
  invFun a := mahlerSeries a
  map_add' f g := by
    ext x
    simp only [ContinuousMap.coe_add, fwdDiff_iter_add, Pi.add_apply,
      ZeroAtInftyContinuousMap.coe_mk, ZeroAtInftyContinuo

中文:
定义 mahlerEquiv
  签名: : C(整数_[p], E) ≃ₗᵢ[整数_[p]] C₀(自然数, E) where
  定义体: ⟨⟨(Δ_[1]^[·] f 0), continuous_of_discreteTopology⟩,
    cocompact_eq_atTop (α := Nat) ▸ fwdDiff_tendsto_zero f⟩
  invFun a := mahlerSeries a
  map_add' f g := by
    ext x
    simp only [ContinuousMap.coe_add, fwdDiff_iter_add, Pi.add_apply,
      ZeroAtInftyContinuousMap.coe_mk, ZeroAtInftyContinuo

Depends on / 依赖: continuous_of_discreteTopology
-/
noncomputable def mahlerEquiv : C(Int_[p], E) ≃ₗᵢ[Int_[p]] C₀(Nat, E) where
  toFun f := ⟨⟨(Δ_[1]^[·] f 0), continuous_of_discreteTopology⟩,
    cocompact_eq_atTop (α := Nat) ▸ fwdDiff_tendsto_zero f⟩
  invFun a := mahlerSeries a
  map_add' f g := by
    ext x
    simp only [ContinuousMap.coe_add, fwdDiff_iter_add, Pi.add_apply,
      ZeroAtInftyContinuousMap.coe_mk, ZeroAtInftyContinuousMap.coe_add]
  map_smul' r f := by
    ext n
    simp only [ContinuousMap.coe_smul, RingHom.id_apply, ZeroAtInftyContinuousMap.coe_mk,
      ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, fwdDiff_iter_const_smul]
  left_inv f := (hasSum_mahler f).tsum_eq
right_inv a := ZeroAtInftyContinuousMap.ext
    fwdDiff_mahlerSeries (cocompact_eq_atTop (α := Nat) ▸ zero_at_infty a)
  norm_map' f := by
    simp only [LinearEquiv.coe_mk, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply le_antisymm
    · exact BoundedContinuousFunction.norm_le_of_nonempty.mpr
        (fun n => norm_fwdDiff_iter_apply_le 1 f 0 n)
    · rw [← (hasSum_mahler f).tsum_eq]
      refine (norm_tsum_le _).trans (ciSup_le fun n => ?_)
      refine le_trans (le_of_eq ?_) (BoundedContinuousFunction.norm_coe_le_norm _ n)
      simp [(hasSum_mahler f).tsum_eq]

/--
lemma `mahlerEquiv_apply` / 引理 `mahlerEquiv_apply`

English:
lemma mahlerEquiv_apply
  given: (f : C(Int_[p], E))
  statement: mahlerEquiv E f = fun n => Δ_[1]^[n] f 0
  proof: rfl

中文:
引理 mahlerEquiv_apply
  条件: (f : C(整数_[p], E))
  结论: mahlerEquiv E f = fun n => Δ_[1]^[n] f 0
  证明: rfl
-/
lemma mahlerEquiv_apply (f : C(Int_[p], E)) : mahlerEquiv E f = fun n => Δ_[1]^[n] f 0 := rfl

/--
lemma `mahlerEquiv_symm_apply` / 引理 `mahlerEquiv_symm_apply`

English:
lemma mahlerEquiv_symm_apply
  given: (a : C₀(Nat, E))
  statement: (mahlerEquiv E).symm a = (mahlerSeries (p := p) a)
  proof: rfl

中文:
引理 mahlerEquiv_symm_apply
  条件: (a : C₀(自然数, E))
  结论: (mahlerEquiv E).symm a = (mahlerSeries (p := p) a)
  证明: rfl
-/
lemma mahlerEquiv_symm_apply (a : C₀(Nat, E)) : (mahlerEquiv E).symm a = (mahlerSeries (p := p) a) :=
  rfl

end mahler_coeff

end PadicInt
