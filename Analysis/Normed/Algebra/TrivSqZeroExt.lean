/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.Instances.TrivSqZeroExt

/-!
# Results on `TrivSqZeroExt R M` related to the norm

This file contains results about `NormedSpace.exp` for `TrivSqZeroExt`.

It also contains a definition of the $ℓ^1$ norm,
which defines $\|r + m\| \coloneqq \|r\| + \|m\|$.
This is not a particularly canonical choice of definition,
but it is sufficient to provide a `NormedAlgebra` instance,
and thus enables `NormedSpace.exp_add_of_commute` to be used on `TrivSqZeroExt`.
If the non-canonicity becomes problematic in future,
we could keep the collection of instances behind an `open scoped`.

## Main results

* `TrivSqZeroExt.fst_exp`
* `TrivSqZeroExt.snd_exp`
* `TrivSqZeroExt.exp_inl`
* `TrivSqZeroExt.exp_inr`
* The $ℓ^1$ norm on `TrivSqZeroExt`:
  * `TrivSqZeroExt.instL1SeminormedAddCommGroup`
  * `TrivSqZeroExt.instL1SeminormedRing`
  * `TrivSqZeroExt.instL1SeminormedCommRing`
  * `TrivSqZeroExt.instL1IsBoundedSMul`
  * `TrivSqZeroExt.instL1NormedAddCommGroup`
  * `TrivSqZeroExt.instL1NormedRing`
  * `TrivSqZeroExt.instL1NormedCommRing`
  * `TrivSqZeroExt.instL1NormedSpace`
  * `TrivSqZeroExt.instL1NormedAlgebra`

## TODO

* Generalize more of these results to non-commutative `R`. In principle, under sufficient conditions
  we should expect
  `(exp x).snd = ∫ t in 0..1, exp (t • x.fst) • op (exp ((1 - t) • x.fst)) • x.snd`
  ([Physics.SE](https://physics.stackexchange.com/a/41671/185147), and
  https://link.springer.com/chapter/10.1007/978-3-540-44953-9_2).

-/

@[expose] public section


variable (𝕜 : Type*) {S R M : Type*}

local notation "tsze" => TrivSqZeroExt

open NormedSpace -- For `NormedSpace.exp`.

namespace TrivSqZeroExt

section Topology

section not_charZero
variable [Field 𝕜] [Ring R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

/--
theorem `fst_expSeries` / 定理 `fst_expSeries`

English:
theorem fst_expSeries
  given: (x : tsze R M) (n : Nat)
  proof: by
  simp [expSeries_apply_eq]

中文:
定理 fst_expSeries
  条件: (x : tsze R M) (n : 自然数)
  证明: by
  simp [expSeries_apply_eq]
-/
@[simp] theorem fst_expSeries (x : tsze R M) (n : Nat) :
    fst (expSeries 𝕜 (tsze R M) n fun _ => x) = expSeries 𝕜 R n fun _ => x.fst := by
  simp [expSeries_apply_eq]

end not_charZero

section Ring
variable [Field 𝕜] [CharZero 𝕜] [Ring R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

/--
theorem `snd_expSeries_of_smul_comm` / 定理 `snd_expSeries_of_smul_comm`

English:
theorem snd_expSeries_of_smul_comm
  proof: by
  simp_rw [expSeries_apply_eq, snd_smul, snd_pow_of_smul_comm _ _ hx,
    ← Nat.cast_smul_eq_nsmul 𝕜 (n + 1), smul_smul, smul_assoc, Nat.factorial_succ, Nat.pred_succ,
    Nat.cast_mul, mul_inv_rev,
    inv_mul_cancel_right₀ ((Nat.cast_ne_zero (R := 𝕜)).mpr <| Nat.succ_ne_zero n)]

中文:
定理 snd_expSeries_of_smul_comm
  证明: by
  simp_rw [expSeries_apply_eq, snd_smul, snd_pow_of_smul_comm _ _ hx,
    ← Nat.cast_smul_eq_nsmul 𝕜 (n + 1), smul_smul, smul_assoc, Nat.factorial_succ, Nat.pred_succ,
    Nat.cast_mul, mul_inv_rev,
    inv_mul_cancel_right₀ ((Nat.cast_ne_zero (R := 𝕜)).mpr <| Nat.succ_ne_zero n)]

Depends on / 依赖: Nat.cast_mul, Nat.cast_ne_zero, Nat.cast_smul_eq_nsmul, Nat.factorial_succ, Nat.pred_succ, Nat.succ_ne_zero, cast_mul, cast_ne_zero, cast_smul_eq_nsmul, expSeries_apply_eq, factorial_succ, mul_inv_rev, pred_succ, simp_rw, smul_assoc, smul_smul, snd_pow_of_smul_comm, snd_smul, succ_ne_zero
-/
theorem snd_expSeries_of_smul_comm
    (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) (n : Nat) :
    snd (expSeries 𝕜 (tsze R M) (n + 1) fun _ => x) = (expSeries 𝕜 R n fun _ => x.fst) • x.snd := by
  simp_rw [expSeries_apply_eq, snd_smul, snd_pow_of_smul_comm _ _ hx,
    ← Nat.cast_smul_eq_nsmul 𝕜 (n + 1), smul_smul, smul_assoc, Nat.factorial_succ, Nat.pred_succ,
    Nat.cast_mul, mul_inv_rev,
    inv_mul_cancel_right₀ ((Nat.cast_ne_zero (R := 𝕜)).mpr <| Nat.succ_ne_zero n)]

/--
theorem `hasSum_snd_expSeries_of_smul_comm` / 定理 `hasSum_snd_expSeries_of_smul_comm`

English:
theorem hasSum_snd_expSeries_of_smul_comm
  statement: (x : tsze R M)
  proof: by
  rw [← hasSum_nat_add_iff' 1]
  simp_rw [snd_expSeries_of_smul_comm _ _ hx]
  simp_rw [expSeries_apply_eq] at *
  rw [Finset.range_one]; rw [Finset.sum_singleton]; rw [Nat.factorial_zero]; rw [Nat.cast_one]; rw [pow_zero]; rw [inv_one]; rw [one_smul]; rw [snd_one]; rw [sub_zero]
  exact h.smul_c

中文:
定理 hasSum_snd_expSeries_of_smul_comm
  结论: (x : tsze R M)
  证明: by
  rw [← hasSum_nat_add_iff' 1]
  simp_rw [snd_expSeries_of_smul_comm _ _ hx]
  simp_rw [expSeries_apply_eq] at *
  rw [Finset.range_one]; rw [Finset.sum_singleton]; rw [Nat.factorial_zero]; rw [Nat.cast_one]; rw [pow_zero]; rw [inv_one]; rw [one_smul]; rw [snd_one]; rw [sub_zero]
  exact h.smul_c

Depends on / 依赖: Finset, Finset.range_one, Finset.sum_singleton, Nat.cast_one, Nat.factorial_zero, cast_one, expSeries_apply_eq, factorial_zero, h.smul_const, hasSum_nat_add_iff, inv_one, one_smul, pow_zero, range_one, simp_rw, smul_const, snd_expSeries_of_smul_comm, snd_one, sub_zero, sum_singleton
-/
theorem hasSum_snd_expSeries_of_smul_comm (x : tsze R M)
    (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) {e : R}
    (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => snd (expSeries 𝕜 (tsze R M) n fun _ => x)) (e • x.snd) := by
  rw [← hasSum_nat_add_iff' 1]
  simp_rw [snd_expSeries_of_smul_comm _ _ hx]
  simp_rw [expSeries_apply_eq] at *
  rw [Finset.range_one]; rw [Finset.sum_singleton]; rw [Nat.factorial_zero]; rw [Nat.cast_one]; rw [pow_zero]; rw [inv_one]; rw [one_smul]; rw [snd_one]; rw [sub_zero]
  exact h.smul_const _

/--
theorem `hasSum_expSeries_of_smul_comm` / 定理 `hasSum_expSeries_of_smul_comm`

English:
theorem hasSum_expSeries_of_smul_comm
  proof: by
  have : HasSum (fun n => fst (expSeries 𝕜 (tsze R M) n fun _ => x)) e := by
    simpa [fst_expSeries] using h
  simpa only [inl_fst_add_inr_snd_eq] using
    (hasSum_inl _ <| this).add (hasSum_inr _ <| hasSum_snd_expSeries_of_smul_comm 𝕜 x hx h)

中文:
定理 hasSum_expSeries_of_smul_comm
  证明: by
  have : HasSum (fun n => fst (expSeries 𝕜 (tsze R M) n fun _ => x)) e := by
    simpa [fst_expSeries] using h
  simpa only [inl_fst_add_inr_snd_eq] using
    (hasSum_inl _ <| this).add (hasSum_inr _ <| hasSum_snd_expSeries_of_smul_comm 𝕜 x hx h)

Depends on / 依赖: HasSum, expSeries, fst_expSeries, hasSum_inl, hasSum_inr, hasSum_snd_expSeries_of_smul_comm, inl_fst_add_inr_snd_eq
-/
theorem hasSum_expSeries_of_smul_comm
    (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd)
    {e : R} (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => expSeries 𝕜 (tsze R M) n fun _ => x) (inl e + inr (e • x.snd)) := by
  have : HasSum (fun n => fst (expSeries 𝕜 (tsze R M) n fun _ => x)) e := by
    simpa [fst_expSeries] using h
  simpa only [inl_fst_add_inr_snd_eq] using
    (hasSum_inl _ <| this).add (hasSum_inr _ <| hasSum_snd_expSeries_of_smul_comm 𝕜 x hx h)

variable [Algebra Rat R] [Module Rat M]
variable [T2Space R] [T2Space M]

/--
theorem `exp_def_of_smul_comm` / 定理 `exp_def_of_smul_comm`

English:
theorem exp_def_of_smul_comm
  given: (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd)
  proof: by
  simp_rw [exp_eq_expSeries_sum Rat, FormalMultilinearSeries.sum]
  by_cases h : Summable (fun (n : Nat) => (expSeries Rat R n) fun _ => fst x)
  · refine (hasSum_expSeries_of_smul_comm Rat x hx ?_).tsum_eq
    exact h.hasSum
  · rw [tsum_eq_zero_of_not_summable h, zero_smul, inr_zero, inl_zero, 

中文:
定理 exp_def_of_smul_comm
  条件: (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd)
  证明: by
  simp_rw [exp_eq_expSeries_sum Rat, FormalMultilinearSeries.sum]
  by_cases h : Summable (fun (n : Nat) => (expSeries Rat R n) fun _ => fst x)
  · refine (hasSum_expSeries_of_smul_comm Rat x hx ?_).tsum_eq
    exact h.hasSum
  · rw [tsum_eq_zero_of_not_summable h, zero_smul, inr_zero, inl_zero, 

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.sum, Summable, Summable.map, TrivSqZeroExt, TrivSqZeroExt.fstHom, continuous_fst, expSeries, exp_eq_expSeries_sum, fstHom, fst_expSeries, h.hasSum, hasSum, hasSum_expSeries_of_smul_comm, inl_zero, inr_zero, simp_rw, toLinearMap, tsum_eq, tsum_eq_zero_of_not_summable
-/
theorem exp_def_of_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) :
    exp x = inl (exp x.fst) + inr (exp x.fst • x.snd) := by
  simp_rw [exp_eq_expSeries_sum Rat, FormalMultilinearSeries.sum]
  by_cases h : Summable (fun (n : Nat) => (expSeries Rat R n) fun _ => fst x)
  · refine (hasSum_expSeries_of_smul_comm Rat x hx ?_).tsum_eq
    exact h.hasSum
  · rw [tsum_eq_zero_of_not_summable h, zero_smul, inr_zero, inl_zero, zero_add,
      tsum_eq_zero_of_not_summable]
    simp_rw [← fst_expSeries] at h
    refine mt ?_ h
    exact (Summable.map · (TrivSqZeroExt.fstHom Rat R M).toLinearMap continuous_fst)

@[simp]
/--
theorem `exp_inl` / 定理 `exp_inl`

English:
theorem exp_inl
  given: (x : R)
  statement: exp (inl x : tsze R M) = inl (exp x)
  proof: by
  rw [exp_def_of_smul_comm]; rw [snd_inl]; rw [fst_inl]; rw [smul_zero]; rw [inr_zero]; rw [add_zero]
  rw [snd_inl]; rw [fst_inl]; rw [smul_zero]; rw [smul_zero]

@[simp]

中文:
定理 exp_inl
  条件: (x : R)
  结论: exp (inl x : tsze R M) = inl (exp x)
  证明: by
  rw [exp_def_of_smul_comm]; rw [snd_inl]; rw [fst_inl]; rw [smul_zero]; rw [inr_zero]; rw [add_zero]
  rw [snd_inl]; rw [fst_inl]; rw [smul_zero]; rw [smul_zero]

@[simp]

Depends on / 依赖: add_zero, exp_def_of_smul_comm, fst_inl, inr_zero, smul_zero, snd_inl
-/
theorem exp_inl (x : R) : exp (inl x : tsze R M) = inl (exp x) := by
  rw [exp_def_of_smul_comm]; rw [snd_inl]; rw [fst_inl]; rw [smul_zero]; rw [inr_zero]; rw [add_zero]
  rw [snd_inl]; rw [fst_inl]; rw [smul_zero]; rw [smul_zero]

@[simp]
/--
theorem `exp_inr` / 定理 `exp_inr`

English:
theorem exp_inr
  given: (m : M)
  statement: exp (inr m : tsze R M) = 1 + inr m
  proof: by
  rw [exp_def_of_smul_comm]; rw [snd_inr]; rw [fst_inr]; rw [exp_zero]; rw [one_smul]; rw [inl_one]
  rw [snd_inr]; rw [fst_inr]; rw [MulOpposite.op_zero]; rw [zero_smul]; rw [zero_smul]

中文:
定理 exp_inr
  条件: (m : M)
  结论: exp (inr m : tsze R M) = 1 + inr m
  证明: by
  rw [exp_def_of_smul_comm]; rw [snd_inr]; rw [fst_inr]; rw [exp_zero]; rw [one_smul]; rw [inl_one]
  rw [snd_inr]; rw [fst_inr]; rw [MulOpposite.op_zero]; rw [zero_smul]; rw [zero_smul]

Depends on / 依赖: MulOpposite, MulOpposite.op_zero, exp_def_of_smul_comm, exp_zero, fst_inr, inl_one, one_smul, op_zero, snd_inr, zero_smul
-/
theorem exp_inr (m : M) : exp (inr m : tsze R M) = 1 + inr m := by
  rw [exp_def_of_smul_comm]; rw [snd_inr]; rw [fst_inr]; rw [exp_zero]; rw [one_smul]; rw [inl_one]
  rw [snd_inr]; rw [fst_inr]; rw [MulOpposite.op_zero]; rw [zero_smul]; rw [zero_smul]

end Ring

section CommRing
variable [CommRing R] [AddCommGroup M] [Algebra Rat R] [Module Rat M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

variable [T2Space R] [T2Space M]

/--
theorem `exp_def` / 定理 `exp_def`

English:
theorem exp_def
  given: (x : tsze R M)
  statement: exp x = inl (exp x.fst) + inr (exp x.fst • x.snd)
  proof: exp_def_of_smul_comm x (op_smul_eq_smul _ _)

@[simp]

中文:
定理 exp_def
  条件: (x : tsze R M)
  结论: exp x = inl (exp x.fst) + inr (exp x.fst • x.snd)
  证明: exp_def_of_smul_comm x (op_smul_eq_smul _ _)

@[simp]

Depends on / 依赖: exp_def_of_smul_comm, op_smul_eq_smul
-/
theorem exp_def (x : tsze R M) : exp x = inl (exp x.fst) + inr (exp x.fst • x.snd) :=
  exp_def_of_smul_comm x (op_smul_eq_smul _ _)

@[simp]
/--
theorem `fst_exp` / 定理 `fst_exp`

English:
theorem fst_exp
  given: (x : tsze R M)
  statement: fst (exp x) = exp x.fst
  proof: by
  rw [exp_def]; rw [fst_add]; rw [fst_inl]; rw [fst_inr]; rw [add_zero]

@[simp]

中文:
定理 fst_exp
  条件: (x : tsze R M)
  结论: fst (exp x) = exp x.fst
  证明: by
  rw [exp_def]; rw [fst_add]; rw [fst_inl]; rw [fst_inr]; rw [add_zero]

@[simp]

Depends on / 依赖: add_zero, exp_def, fst_add, fst_inl, fst_inr
-/
theorem fst_exp (x : tsze R M) : fst (exp x) = exp x.fst := by
  rw [exp_def]; rw [fst_add]; rw [fst_inl]; rw [fst_inr]; rw [add_zero]

@[simp]
/--
theorem `snd_exp` / 定理 `snd_exp`

English:
theorem snd_exp
  given: (x : tsze R M)
  statement: snd (exp x) = exp x.fst • x.snd
  proof: by
  rw [exp_def]; rw [snd_add]; rw [snd_inl]; rw [snd_inr]; rw [zero_add]

中文:
定理 snd_exp
  条件: (x : tsze R M)
  结论: snd (exp x) = exp x.fst • x.snd
  证明: by
  rw [exp_def]; rw [snd_add]; rw [snd_inl]; rw [snd_inr]; rw [zero_add]

Depends on / 依赖: exp_def, snd_add, snd_inl, snd_inr, zero_add
-/
theorem snd_exp (x : tsze R M) : snd (exp x) = exp x.fst • x.snd := by
  rw [exp_def]; rw [snd_add]; rw [snd_inl]; rw [snd_inr]; rw [zero_add]

/--
theorem `eq_smul_exp_of_invertible` / 定理 `eq_smul_exp_of_invertible`

English:
theorem eq_smul_exp_of_invertible
  given: (x : tsze R M) [Invertible x.fst]
  proof: by
  rw [← inr_smul]; rw [exp_inr]; rw [smul_add]; rw [← inl_one]; rw [← inl_smul]; rw [← inr_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [smul_smul]; rw [mul_invOf_self]; rw [one_smul]; rw [inl_fst_add_inr_snd_eq]

中文:
定理 eq_smul_exp_of_invertible
  条件: (x : tsze R M) [可逆 x.fst]
  证明: by
  rw [← inr_smul]; rw [exp_inr]; rw [smul_add]; rw [← inl_one]; rw [← inl_smul]; rw [← inr_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [smul_smul]; rw [mul_invOf_self]; rw [one_smul]; rw [inl_fst_add_inr_snd_eq]

Depends on / 依赖: exp_inr, inl_fst_add_inr_snd_eq, inl_one, inl_smul, inr_smul, mul_invOf_self, mul_one, one_smul, smul_add, smul_eq_mul, smul_smul
-/
theorem eq_smul_exp_of_invertible (x : tsze R M) [Invertible x.fst] :
    x = x.fst • exp (⅟x.fst • inr x.snd) := by
  rw [← inr_smul]; rw [exp_inr]; rw [smul_add]; rw [← inl_one]; rw [← inl_smul]; rw [← inr_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [smul_smul]; rw [mul_invOf_self]; rw [one_smul]; rw [inl_fst_add_inr_snd_eq]

end CommRing

section Field
variable [Field R] [AddCommGroup M]
  [Algebra Rat R] [Module Rat M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

variable [T2Space R] [T2Space M]

/--
theorem `eq_smul_exp_of_ne_zero` / 定理 `eq_smul_exp_of_ne_zero`

English:
theorem eq_smul_exp_of_ne_zero
  given: (x : tsze R M) (hx : x.fst != 0)
  proof: letI : Invertible x.fst := invertibleOfNonzero hx
  eq_smul_exp_of_invertible _

中文:
定理 eq_smul_exp_of_ne_zero
  条件: (x : tsze R M) (hx : x.fst != 0)
  证明: letI : Invertible x.fst := invertibleOfNonzero hx
  eq_smul_exp_of_invertible _

Depends on / 依赖: Invertible, eq_smul_exp_of_invertible, invertibleOfNonzero, x.fst
-/
theorem eq_smul_exp_of_ne_zero (x : tsze R M) (hx : x.fst != 0) :
    x = x.fst • exp (x.fst⁻¹ • inr x.snd) :=
  letI : Invertible x.fst := invertibleOfNonzero hx
  eq_smul_exp_of_invertible _

end Field

end Topology

/-!
### The $ℓ^1$ norm on the trivial square zero extension
-/

noncomputable section Seminormed

section Ring
variable [SeminormedCommRing S] [SeminormedRing R] [SeminormedAddCommGroup M]
variable [Algebra S R] [Module S M]
variable [IsBoundedSMul S R] [IsBoundedSMul S M]

/--
Instance `instL1SeminormedAddCommGroup` / 实例 `instL1SeminormedAddCommGroup`

English:
instance instL1SeminormedAddCommGroup
  signature: : SeminormedAddCommGroup (tsze R M)
  body: fast_instance% {
    WithLp.seminormedAddCommGroupToProd 1 R M with
    toUniformSpace := inferInstance }

example :
    (TrivSqZeroExt.instUniformSpace : UniformSpace (tsze R M)) =
    PseudoMetricSpace.toUniformSpace := rfl

中文:
实例 instL1SeminormedAddCommGroup
  签名: : SeminormedAddComm群 (tsze R M)
  定义体: fast_instance% {
    WithLp.seminormedAddCommGroupToProd 1 R M with
    toUniformSpace := inferInstance }

example :
    (TrivSqZeroExt.instUniformSpace : UniformSpace (tsze R M)) =
    PseudoMetricSpace.toUniformSpace := rfl

Depends on / 依赖: WithLp, WithLp.seminormedAddCommGroupToProd, fast_instance, seminormedAddCommGroupToProd, toUniformSpace
-/
instance instL1SeminormedAddCommGroup : SeminormedAddCommGroup (tsze R M) :=
  fast_instance% {
    WithLp.seminormedAddCommGroupToProd 1 R M with
    toUniformSpace := inferInstance }

example :
    (TrivSqZeroExt.instUniformSpace : UniformSpace (tsze R M)) =
    PseudoMetricSpace.toUniformSpace := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (x : tsze R M)
  statement: ‖x‖ = ‖fst x‖ + ‖snd x‖
  proof: by
  erw [WithLp.norm_seminormedAddCommGroupToProd]
  rw [WithLp.prod_norm_eq_add (by norm_num)]
  simp only [WithLp.toLp_fst, ENNReal.toReal_one, Real.rpow_one, WithLp.toLp_snd, ne_eq,
    one_ne_zero, not_false_eq_true, div_self, fst, snd]

中文:
定理 norm_def
  条件: (x : tsze R M)
  结论: ‖x‖ = ‖fst x‖ + ‖snd x‖
  证明: by
  erw [WithLp.norm_seminormedAddCommGroupToProd]
  rw [WithLp.prod_norm_eq_add (by norm_num)]
  simp only [WithLp.toLp_fst, ENNReal.toReal_one, Real.rpow_one, WithLp.toLp_snd, ne_eq,
    one_ne_zero, not_false_eq_true, div_self, fst, snd]

Depends on / 依赖: ENNReal, ENNReal.toReal_one, Real.rpow_one, WithLp, WithLp.norm_seminormedAddCommGroupToProd, WithLp.prod_norm_eq_add, WithLp.toLp_fst, WithLp.toLp_snd, div_self, ne_eq, norm_seminormedAddCommGroupToProd, not_false_eq_true, one_ne_zero, prod_norm_eq_add, rpow_one, toLp_fst, toLp_snd, toReal_one
-/
theorem norm_def (x : tsze R M) : ‖x‖ = ‖fst x‖ + ‖snd x‖ := by
  erw [WithLp.norm_seminormedAddCommGroupToProd]
  rw [WithLp.prod_norm_eq_add (by norm_num)]
  simp only [WithLp.toLp_fst, ENNReal.toReal_one, Real.rpow_one, WithLp.toLp_snd, ne_eq,
    one_ne_zero, not_false_eq_true, div_self, fst, snd]

/--
theorem `nnnorm_def` / 定理 `nnnorm_def`

English:
theorem nnnorm_def
  given: (x : tsze R M)
  statement: ‖x‖₊ = ‖fst x‖₊ + ‖snd x‖₊
  proof: by
  ext; simp [norm_def]

中文:
定理 nnnorm_def
  条件: (x : tsze R M)
  结论: ‖x‖₊ = ‖fst x‖₊ + ‖snd x‖₊
  证明: by
  ext; simp [norm_def]

Depends on / 依赖: norm_def
-/
theorem nnnorm_def (x : tsze R M) : ‖x‖₊ = ‖fst x‖₊ + ‖snd x‖₊ := by
  ext; simp [norm_def]

/--
theorem `norm_inl` / 定理 `norm_inl`

English:
theorem norm_inl
  given: (r : R)
  statement: ‖(inl r : tsze R M)‖ = ‖r‖
  proof: by simp [norm_def]

中文:
定理 norm_inl
  条件: (r : R)
  结论: ‖(inl r : tsze R M)‖ = ‖r‖
  证明: by simp [norm_def]
-/
@[simp] theorem norm_inl (r : R) : ‖(inl r : tsze R M)‖ = ‖r‖ := by simp [norm_def]
/--
theorem `norm_inr` / 定理 `norm_inr`

English:
theorem norm_inr
  given: (m : M)
  statement: ‖(inr m : tsze R M)‖ = ‖m‖
  proof: by simp [norm_def]

中文:
定理 norm_inr
  条件: (m : M)
  结论: ‖(inr m : tsze R M)‖ = ‖m‖
  证明: by simp [norm_def]
-/
@[simp] theorem norm_inr (m : M) : ‖(inr m : tsze R M)‖ = ‖m‖ := by simp [norm_def]

/--
theorem `nnnorm_inl` / 定理 `nnnorm_inl`

English:
theorem nnnorm_inl
  given: (r : R)
  statement: ‖(inl r : tsze R M)‖₊ = ‖r‖₊
  proof: by simp [nnnorm_def]

中文:
定理 nnnorm_inl
  条件: (r : R)
  结论: ‖(inl r : tsze R M)‖₊ = ‖r‖₊
  证明: by simp [nnnorm_def]
-/
@[simp] theorem nnnorm_inl (r : R) : ‖(inl r : tsze R M)‖₊ = ‖r‖₊ := by simp [nnnorm_def]

/--
theorem `nnnorm_inr` / 定理 `nnnorm_inr`

English:
theorem nnnorm_inr
  given: (m : M)
  statement: ‖(inr m : tsze R M)‖₊ = ‖m‖₊
  proof: by simp [nnnorm_def]

中文:
定理 nnnorm_inr
  条件: (m : M)
  结论: ‖(inr m : tsze R M)‖₊ = ‖m‖₊
  证明: by simp [nnnorm_def]
-/
@[simp] theorem nnnorm_inr (m : M) : ‖(inr m : tsze R M)‖₊ = ‖m‖₊ := by simp [nnnorm_def]

variable [Module R M] [IsBoundedSMul R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instL1SeminormedRing` / 实例 `instL1SeminormedRing`

English:
instance instL1SeminormedRing
  signature: : SeminormedRing (tsze R M) where
  body: by
      gcongr
      · apply norm_mul_le
      · refine norm_add_le_of_le ?_ ?_ <;>
        apply norm_smul_le
    _ <= ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) + (‖m₁‖ * ‖m₂‖) := by
      apply le_add_of_nonneg_right
      positivity
    _ = (‖r₁‖ + ‖m₁‖) * (‖r₂‖ + ‖m₂‖) := by ring
  __ : Ring (t

中文:
实例 instL1SeminormedRing
  签名: : Seminormed环 (tsze R M) where
  定义体: by
      gcongr
      · apply norm_mul_le
      · refine norm_add_le_of_le ?_ ?_ <;>
        apply norm_smul_le
    _ <= ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) + (‖m₁‖ * ‖m₂‖) := by
      apply le_add_of_nonneg_right
      positivity
    _ = (‖r₁‖ + ‖m₁‖) * (‖r₂‖ + ‖m₂‖) := by ring
  __ : Ring (t

Depends on / 依赖: SeminormedAddCommGroup, le_add_of_nonneg_right, norm_add_le_of_le, norm_mul_le, norm_smul_le
-/
instance instL1SeminormedRing : SeminormedRing (tsze R M) where
  norm_mul_le
  | ⟨r₁, m₁⟩, ⟨r₂, m₂⟩ => by
    simp_rw [norm_def]
    calc ‖r₁ * r₂‖ + ‖r₁ • m₂ + MulOpposite.op r₂ • m₁‖
    _ <= ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) := by
      gcongr
      · apply norm_mul_le
      · refine norm_add_le_of_le ?_ ?_ <;>
        apply norm_smul_le
    _ <= ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) + (‖m₁‖ * ‖m₂‖) := by
      apply le_add_of_nonneg_right
      positivity
    _ = (‖r₁‖ + ‖m₁‖) * (‖r₂‖ + ‖m₂‖) := by ring
  __ : Ring (tsze R M) := inferInstance
  __ : SeminormedAddCommGroup (tsze R M) := inferInstance

/--
Instance `instL1IsBoundedSMul` / 实例 `instL1IsBoundedSMul`

English:
instance instL1IsBoundedSMul
  signature: : IsBoundedSMul S (tsze R M)
  body: WithLp.isBoundedSMulSeminormedAddCommGroupToProd 1 R M

中文:
实例 instL1IsBoundedSMul
  签名: : 是BoundedSMul S (tsze R M)
  定义体: WithLp.isBoundedSMulSeminormedAddCommGroupToProd 1 R M

Depends on / 依赖: WithLp, WithLp.isBoundedSMulSeminormedAddCommGroupToProd, isBoundedSMulSeminormedAddCommGroupToProd
-/
instance instL1IsBoundedSMul : IsBoundedSMul S (tsze R M) :=
  WithLp.isBoundedSMulSeminormedAddCommGroupToProd 1 R M

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormOneClass
  signature: R] : NormOneClass (tsze R M) where
  body: by rw [norm_def, fst_one, snd_one, norm_zero, norm_one, add_zero]

中文:
实例 [NormOne类
  签名: R] : NormOne类 (tsze R M) where
  定义体: by rw [norm_def, fst_one, snd_one, norm_zero, norm_one, add_zero]

Depends on / 依赖: add_zero, fst_one, norm_def, norm_one, norm_zero, snd_one
-/
instance [NormOneClass R] : NormOneClass (tsze R M) where
  norm_one := by rw [norm_def, fst_one, snd_one, norm_zero, norm_one, add_zero]

end Ring

section CommRing

variable [SeminormedCommRing R] [SeminormedAddCommGroup M]
variable [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [IsBoundedSMul R M]

/--
Instance `instL1SeminormedCommRing` / 实例 `instL1SeminormedCommRing`

English:
instance instL1SeminormedCommRing
  signature: : SeminormedCommRing (tsze R M) where
  body: inferInstance
  __ : CommRing (tsze R M) := inferInstance

中文:
实例 instL1SeminormedCommRing
  签名: : SeminormedComm环 (tsze R M) where
  定义体: inferInstance
  __ : CommRing (tsze R M) := inferInstance
-/
instance instL1SeminormedCommRing : SeminormedCommRing (tsze R M) where
  __ : SeminormedRing (tsze R M) := inferInstance
  __ : CommRing (tsze R M) := inferInstance

end CommRing

end Seminormed

noncomputable section Normed

section Ring

variable [NormedRing R] [NormedAddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

/--
Instance `instL1NormedAddCommGroup` / 实例 `instL1NormedAddCommGroup`

English:
instance instL1NormedAddCommGroup
  signature: : NormedAddCommGroup (tsze R M)
  body: fast_instance% WithLp.normedAddCommGroupToProd 1 R M

中文:
实例 instL1NormedAddCommGroup
  签名: : 赋范交换加群 (tsze R M)
  定义体: fast_instance% WithLp.normedAddCommGroupToProd 1 R M

Depends on / 依赖: WithLp, WithLp.normedAddCommGroupToProd, fast_instance, normedAddCommGroupToProd
-/
instance instL1NormedAddCommGroup : NormedAddCommGroup (tsze R M) :=
  fast_instance% WithLp.normedAddCommGroupToProd 1 R M

/--
Instance `instL1NormedRing` / 实例 `instL1NormedRing`

English:
instance instL1NormedRing
  signature: : NormedRing (tsze R M) where
  body: inferInstance
  __ : NormedAddCommGroup (tsze R M) := inferInstance

中文:
实例 instL1NormedRing
  签名: : 赋范环 (tsze R M) where
  定义体: inferInstance
  __ : NormedAddCommGroup (tsze R M) := inferInstance
-/
instance instL1NormedRing : NormedRing (tsze R M) where
  __ : SeminormedRing (tsze R M) := inferInstance
  __ : NormedAddCommGroup (tsze R M) := inferInstance

end Ring

section CommRing

variable [NormedCommRing R] [NormedAddCommGroup M]
variable [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [IsBoundedSMul R M]

/--
Instance `instL1NormedCommRing` / 实例 `instL1NormedCommRing`

English:
instance instL1NormedCommRing
  signature: : NormedCommRing (tsze R M) where
  body: inferInstance
  __ : CommRing (tsze R M) := inferInstance

中文:
实例 instL1NormedCommRing
  签名: : NormedComm环 (tsze R M) where
  定义体: inferInstance
  __ : CommRing (tsze R M) := inferInstance
-/
instance instL1NormedCommRing : NormedCommRing (tsze R M) where
  __ : NormedRing (tsze R M) := inferInstance
  __ : CommRing (tsze R M) := inferInstance

end CommRing

section Algebra

variable [NormedField 𝕜] [NormedRing R] [NormedAddCommGroup M]
variable [NormedAlgebra 𝕜 R] [NormedSpace 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]

/--
Instance `instL1NormedSpace` / 实例 `instL1NormedSpace`

English:
instance instL1NormedSpace
  signature: : NormedSpace 𝕜 (tsze R M)
  body: fast_instance% WithLp.normedSpaceSeminormedAddCommGroupToProd 1 R M

中文:
实例 instL1NormedSpace
  签名: : 赋范空间 𝕜 (tsze R M)
  定义体: fast_instance% WithLp.normedSpaceSeminormedAddCommGroupToProd 1 R M

Depends on / 依赖: WithLp, WithLp.normedSpaceSeminormedAddCommGroupToProd, fast_instance, normedSpaceSeminormedAddCommGroupToProd
-/
instance instL1NormedSpace : NormedSpace 𝕜 (tsze R M) :=
  fast_instance% WithLp.normedSpaceSeminormedAddCommGroupToProd 1 R M

/--
Instance `instL1NormedAlgebra` / 实例 `instL1NormedAlgebra`

English:
instance instL1NormedAlgebra
  signature: : NormedAlgebra 𝕜 (tsze R M) where
  body: _root_.norm_smul_le

中文:
实例 instL1NormedAlgebra
  签名: : 赋范代数 𝕜 (tsze R M) where
  定义体: _root_.norm_smul_le

Depends on / 依赖: _root_, _root_.norm_smul_le, norm_smul_le
-/
instance instL1NormedAlgebra : NormedAlgebra 𝕜 (tsze R M) where
  norm_smul_le := _root_.norm_smul_le

end Algebra


end Normed

section

variable [NormedRing R] [NormedAddCommGroup M]
variable [NormedAlgebra Rat R] [NormedSpace Rat M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [CompleteSpace R] [CompleteSpace M]

-- Evidence that we have sufficient instances on `tsze R N`
-- to make `NormedSpace.exp_add_of_commute` usable
example (a b : tsze R M) (h : Commute a b) : exp (a + b) = exp a * exp b :=
  exp_add_of_commute h

end

end TrivSqZeroExt
