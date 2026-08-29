/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.ContinuousMap.Polynomial

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : Fin (n+1), (n.choose k * x^k * (1-x)^(n-k)) • f (k/n : ℝ)
```
for a continuous function `f : C([0,1], E)` taking values in a locally convex vector space
converge uniformly to `f` as `n` tends to infinity.
This statement directly applies to the cases when the codomain is a (semi)normed space
or, more generally, has a topology defined by a family of seminorms.

Our proof follows [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D.
The original proof, due to [Bernstein](bernstein1912) in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.

The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.

(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)

This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.
-/

@[expose] public section

noncomputable section

open Filter
open scoped unitInterval Topology Uniformity

/--
Definition of `bernstein` / `bernstein` 的定义

English:
definition bernstein
  signature: (n ν : Nat)
  body: (bernsteinPolynomial Real n ν).toContinuousMapOn I

中文:
定义 bernstein
  签名: (n ν : 自然数)
  定义体: (bernsteinPolynomial Real n ν).toContinuousMapOn I

Depends on / 依赖: bernsteinPolynomial, toContinuousMapOn
-/
def bernstein (n ν : Nat) : C(I, Real) :=
  (bernsteinPolynomial Real n ν).toContinuousMapOn I

/--
theorem `bernstein_apply` / 定理 `bernstein_apply`

English:
theorem bernstein_apply
  given: (n ν : Nat) (x : I)
  proof: by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  simp

@[simp]

中文:
定理 bernstein_apply
  条件: (n ν : 自然数) (x : I)
  证明: by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  simp

@[simp]

Depends on / 依赖: Polynomial, Polynomial.toContinuousMap, Polynomial.toContinuousMapOn, bernstein, bernsteinPolynomial, toContinuousMap, toContinuousMapOn
-/
theorem bernstein_apply (n ν : Nat) (x : I) :
    bernstein n ν x = (n.choose ν : Real) * (x : Real) ^ ν * (1 - (x : Real)) ^ (n - ν) := by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  simp

@[simp]
/--
theorem `bernstein_nonneg` / 定理 `bernstein_nonneg`

English:
theorem bernstein_nonneg
  given: {n ν : Nat} {x : I}
  statement: 0 <= bernstein n ν x
  proof: by
  simp only [bernstein_apply]
  have h₁ : (0 : Real) <= x := by unit_interval
  have h₂ : (0 : Real) <= 1 - x := by unit_interval
  positivity

中文:
定理 bernstein_nonneg
  条件: {n ν : 自然数} {x : I}
  结论: 0 <= bernstein n ν x
  证明: by
  simp only [bernstein_apply]
  have h₁ : (0 : Real) <= x := by unit_interval
  have h₂ : (0 : Real) <= 1 - x := by unit_interval
  positivity

Depends on / 依赖: bernstein_apply, unit_interval
-/
theorem bernstein_nonneg {n ν : Nat} {x : I} : 0 <= bernstein n ν x := by
  simp only [bernstein_apply]
  have h₁ : (0 : Real) <= x := by unit_interval
  have h₂ : (0 : Real) <= 1 - x := by unit_interval
  positivity

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension of the `positivity` tactic for Bernstein polynomials: they are always non-negative. -/
@[positivity DFunLike.coe (bernstein _ _) _]
meta def evalBernstein : PositivityExt where eval {_ _} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let .app (.app _coe (.app (.app _ n) ν)) x ← whnfR e | throwError "not bernstein polynomial"
  let p ← mkAppOptM ``bernstein_nonneg #[n, ν, x]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity

/-!
We now give a slight reformulation of `bernsteinPolynomial.variance`.
-/


namespace bernstein

/--
Definition of `z` / `z` 的定义

English:
definition z
  signature: {n : Nat} (k : Fin (n + 1))
  body: ⟨(k : Real) / n, by simp [div_nonneg, div_le_one_of_le₀, k.is_le]⟩

local postfix:90 "/ₙ" => z

中文:
定义 z
  签名: {n : 自然数} (k : 有限集 (n + 1))
  定义体: ⟨(k : Real) / n, by simp [div_nonneg, div_le_one_of_le₀, k.is_le]⟩

local postfix:90 "/ₙ" => z

Depends on / 依赖: div_nonneg, is_le, k.is_le
-/
def z {n : Nat} (k : Fin (n + 1)) : I :=
  ⟨(k : Real) / n, by simp [div_nonneg, div_le_one_of_le₀, k.is_le]⟩

local postfix:90 "/ₙ" => z

/--
lemma `z_zero` / 引理 `z_zero`

English:
lemma z_zero
  given: {n : Nat}
  statement: (0 : Fin (n + 1))/ₙ = 0
  proof: by simp [z]

中文:
引理 z_zero
  条件: {n : 自然数}
  结论: (0 : 有限集 (n + 1))/ₙ = 0
  证明: by simp [z]
-/
@[simp] lemma z_zero {n : Nat} : (0 : Fin (n + 1))/ₙ = 0 := by simp [z]
/--
lemma `z_last` / 引理 `z_last`

English:
lemma z_last
  given: {n : Nat} (hn : n != 0)
  statement: .last n/ₙ = 1
  proof: by simp [z, hn]

@[simp]

中文:
引理 z_last
  条件: {n : 自然数} (hn : n != 0)
  结论: .last n/ₙ = 1
  证明: by simp [z, hn]

@[simp]

Depends on / 依赖: HasBinaryBiproducts, hasBinaryBiproducts
-/
@[simp] lemma z_last {n : Nat} (hn : n != 0) : .last n/ₙ = 1 := by simp [z, hn]

@[simp]
/--
theorem `probability` / 定理 `probability`

English:
theorem probability
  given: (n : Nat) (x : I)
  statement: (∑ k : Fin (n + 1), bernstein n k x) = 1
  proof: by
  have := bernsteinPolynomial.sum Real n
  apply_fun fun p => Polynomial.aeval (x : Real) p at this
  simpa [Finset.sum_range]

中文:
定理 probability
  条件: (n : 自然数) (x : I)
  结论: (∑ k : 有限集 (n + 1), bernstein n k x) = 1
  证明: by
  have := bernsteinPolynomial.sum Real n
  apply_fun fun p => Polynomial.aeval (x : Real) p at this
  simpa [Finset.sum_range]

Depends on / 依赖: Finset, Finset.sum_range, HasZeroObject, Polynomial, Polynomial.aeval, apply_fun, bernsteinPolynomial, bernsteinPolynomial.sum, hasZeroObject, sum_range
-/
theorem probability (n : Nat) (x : I) : (∑ k : Fin (n + 1), bernstein n k x) = 1 := by
  have := bernsteinPolynomial.sum Real n
  apply_fun fun p => Polynomial.aeval (x : Real) p at this
  simpa [Finset.sum_range]

/--
theorem `variance` / 定理 `variance`

English:
theorem variance
  given: {n : Nat} (hn : n != 0) (x : I)
  proof: by
  convert! congr(Polynomial.aeval (x : Real) $(bernsteinPolynomial.variance Real n) / n ^ 2) using 1
  · simp only [z, bernstein_apply, nsmul_eq_mul, bernsteinPolynomial, Finset.sum_range, map_sum,
      Polynomial.coe_aeval_eq_eval, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,


中文:
定理 variance
  条件: {n : 自然数} (hn : n != 0) (x : I)
  证明: by
  convert! congr(Polynomial.aeval (x : Real) $(bernsteinPolynomial.variance Real n) / n ^ 2) using 1
  · simp only [z, bernstein_apply, nsmul_eq_mul, bernsteinPolynomial, Finset.sum_range, map_sum,
      Polynomial.coe_aeval_eq_eval, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,


Depends on / 依赖: Finset, Finset.sum_div, Finset.sum_range, Polynomial, Polynomial.aeval, Polynomial.coe_aeval_eq_eval, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_sub, bernsteinPolynomial, bernsteinPolynomial.variance, bernstein_apply, coe_aeval_eq_eval, convert, eval_X, eval_mul, eval_natCast
-/
theorem variance {n : Nat} (hn : n != 0) (x : I) :
    (∑ k : Fin (n + 1), (x - k/ₙ : Real) ^ 2 * bernstein n k x) = (x : Real) * (1 - x) / n := by
  convert! congr(Polynomial.aeval (x : Real) $(bernsteinPolynomial.variance Real n) / n ^ 2) using 1
  · simp only [z, bernstein_apply, nsmul_eq_mul, bernsteinPolynomial, Finset.sum_range, map_sum,
      Polynomial.coe_aeval_eq_eval, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_natCast, Polynomial.eval_X, Polynomial.eval_one]
    field_simp
    rw [← Finset.sum_div]
    field
  · simp
    field

end bernstein

open bernstein

local postfix:1024 "/ₙ" => z

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module Real E] [ContinuousSMul Real E]

/--
Definition of `bernsteinApproximation` / `bernsteinApproximation` 的定义

English:
definition bernsteinApproximation
  signature: (n : Nat) (f : C(I, E))
  body: ∑ k : Fin (n + 1), bernstein n k • .const _ (f k/ₙ)

中文:
定义 bernsteinApproximation
  签名: (n : 自然数) (f : C(I, E))
  定义体: ∑ k : Fin (n + 1), bernstein n k • .const _ (f k/ₙ)

Depends on / 依赖: bernstein
-/
def bernsteinApproximation (n : Nat) (f : C(I, E)) : C(I, E) :=
  ∑ k : Fin (n + 1), bernstein n k • .const _ (f k/ₙ)

/-!
We now set up some of the basic machinery of the proof that the Bernstein approximations
converge uniformly.

A key player is the set `S f ε h n x`,
for some function `f : C(I, E)`, `h : 0 < ε`, `n : ℕ` and `x : I`.

This is the set of points `k` in `Fin (n+1)` such that
`k/n` is within `δ` of `x`, where `δ` is the modulus of uniform continuity for `f`,
chosen so `‖f x - f y‖ < ε/2` when `|x - y| < δ`.

We show that if `k ∉ S`, then `1 ≤ δ^-2 * (x - k/n)^2`.
-/

namespace bernsteinApproximation

/--
theorem `apply` / 定理 `apply`

English:
theorem apply
  given: (n : Nat) (f : C(I, E)) (x : I)
  proof: by
  simp [bernsteinApproximation]

@[simp]

中文:
定理 apply
  条件: (n : 自然数) (f : C(I, E)) (x : I)
  证明: by
  simp [bernsteinApproximation]

@[simp]

Depends on / 依赖: bernsteinApproximation
-/
theorem apply (n : Nat) (f : C(I, E)) (x : I) :
    bernsteinApproximation n f x = ∑ k : Fin (n + 1), bernstein n k x • f k/ₙ := by
  simp [bernsteinApproximation]

@[simp]
/--
theorem `apply_zero` / 定理 `apply_zero`

English:
theorem apply_zero
  given: (n : Nat) (f : C(I, E))
  statement: bernsteinApproximation n f 0 = f 0
  proof: by
  simp [apply, Fin.sum_univ_succ, bernstein_apply, z]

@[simp]

中文:
定理 apply_zero
  条件: (n : 自然数) (f : C(I, E))
  结论: bernsteinApproximation n f 0 = f 0
  证明: by
  simp [apply, Fin.sum_univ_succ, bernstein_apply, z]

@[simp]

Depends on / 依赖: Fin.sum_univ_succ, bernstein_apply, sum_univ_succ
-/
theorem apply_zero (n : Nat) (f : C(I, E)) : bernsteinApproximation n f 0 = f 0 := by
  simp [apply, Fin.sum_univ_succ, bernstein_apply, z]

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: {n : Nat} (hn : n != 0) (f : C(I, E))
  statement: bernsteinApproximation n f 1 = f 1
  proof: by
  simp [apply, Fin.sum_univ_castSucc, bernstein_apply, hn, Nat.sub_eq_zero_iff_le]

中文:
定理 apply_one
  条件: {n : 自然数} (hn : n != 0) (f : C(I, E))
  结论: bernsteinApproximation n f 1 = f 1
  证明: by
  simp [apply, Fin.sum_univ_castSucc, bernstein_apply, hn, Nat.sub_eq_zero_iff_le]

Depends on / 依赖: Fin.sum_univ_castSucc, Nat.sub_eq_zero_iff_le, bernstein_apply, sub_eq_zero_iff_le, sum_univ_castSucc
-/
theorem apply_one {n : Nat} (hn : n != 0) (f : C(I, E)) : bernsteinApproximation n f 1 = f 1 := by
  simp [apply, Fin.sum_univ_castSucc, bernstein_apply, hn, Nat.sub_eq_zero_iff_le]

end bernsteinApproximation

open bernsteinApproximation

/--
theorem `bernsteinApproximation_uniform` / 定理 `bernsteinApproximation_uniform`

English:
theorem bernsteinApproximation_uniform
  given: [LocallyConvexSpace Real E] (f : C(I, E))
  proof: by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  /- Topology on a locally convex TVS is given by a family of seminorms `‖x‖_U = gauge U x`,
  where the open symmetric convex sets `U` form a basis of neighborhoo

中文:
定理 bernsteinApproximation_uniform
  条件: [LocallyConvex空间 实数 E] (f : C(I, E))
  证明: by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  /- Topology on a locally convex TVS is given by a family of seminorms `‖x‖_U = gauge U x`,
  where the open symmetric convex sets `U` form a basis of neighborhoo

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, IsUniformAddGroup, UniformSpace, isUniformAddGroup_of_addCommGroup, rightUniformSpace
-/
theorem bernsteinApproximation_uniform [LocallyConvexSpace Real E] (f : C(I, E)) :
    Tendsto (fun n : Nat => bernsteinApproximation n f) atTop (𝓝 f) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  /- Topology on a locally convex TVS is given by a family of seminorms `‖x‖_U = gauge U x`,
  where the open symmetric convex sets `U` form a basis of neighborhoods in this topology,
  and are the open unit balls for the corresponding seminorms.
  For technical reasons, we neither assume `U`s to be open, nor symmetric. -/
  suffices forall U in 𝓝 (0 : E), Convex Real U ->
      forallᶠ n in atTop, forall x : I, gauge U (bernsteinApproximation n f x - f x) < 1 by
    rw [(LocallyConvexSpace.convex_basis_zero Real E).uniformity_of_nhds_zero_swapped
.tendsto_right_iff] nhds_basis_uniformity .compactConvergenceUniformity_of_compact
    rintro U ⟨hU₀, hcU⟩
    filter_upwards [this U hU₀ hcU] with n hn x
    exact setOfPred_gauge_lt_one_subset_self hcU (mem_of_mem_nhds hU₀) (absorbent_nhds_zero hU₀)
      (hn x)
  intro U hU₀ hUc
  /- Choose a constant `C` such that `‖f x - f y‖_U ≤ C` for all `x`, `y`.
  For a normed space, this would be twice the norm of `f`. -/
  obtain ⟨C, hC⟩ : exists C, forall x y, gauge U (f x - f y) <= C := by
    have : Continuous fun (x, y) => gauge U (f x - f y) := by fun_prop
    simpa only [BddAbove, Set.Nonempty, mem_upperBounds, Set.forall_mem_range, Prod.forall]
.bddAbove using isCompact_range this
  have hC₀ : 0 <= C := le_trans (gauge_nonneg _) (hC 0 0)
  /- Use uniform continuity of `f` to choose `δ > 0` such that `‖f x - f y‖_U < 1 / 2`
  whenever `dist x y < δ`. -/
  obtain ⟨δ, hδ₀, hδ⟩ : exists δ > 0, forall x y : I, dist x y < δ -> gauge U (f x - f y) < 1 / 2 := by
    have := CompactSpace.uniformContinuous_of_continuous (map_continuous f)
    rw [Metric.uniformity_basis_dist.uniformContinuous_iff
      (basis_sets _).uniformity_of_nhds_zero_swapped] at this
exact this {z | gauge U z < 1 / 2} tendsto_gauge_nhds_zero hU₀
.eventually_lt_const by positivity
  -- Take `n ≠ 0` such that `C / δ ^ 2 / n < 1 / 2`.
  have nhds_zero := tendsto_const_div_atTop_nhds_zero_nat (C / δ ^ 2)
  filter_upwards [nhds_zero.eventually_lt_const (half_pos one_pos), eventually_ne_atTop 0]
    with n nh hn₀ x
  -- The idea is to split up the sum over `k` into two sets,
  -- `S`, where `x - k/n < δ`, and its complement.
  set S : Finset (Fin (n + 1)) := {k : Fin (n + 1) | dist k/ₙ x < δ}
  calc
    gauge U (bernsteinApproximation n f x - f x)
      = gauge U (∑ k : Fin (n + 1), bernstein n k x • (f k/ₙ - f x)) := by
      simp [bernsteinApproximation.apply, smul_sub, ← Finset.sum_smul]
    _ <= ∑ k : Fin (n + 1), gauge U (bernstein n k x • (f k/ₙ - f x)) :=
      gauge_sum_le hUc (absorbent_nhds_zero hU₀) _ _
    _ = ∑ k : Fin (n + 1), bernstein n k x * gauge U (f k/ₙ - f x) := by
      simp only [gauge_smul_of_nonneg, bernstein_nonneg, smul_eq_mul]
    _ = (∑ k in S, bernstein n k x * gauge U (f k/ₙ - f x)) +
          ∑ k in Sᶜ, bernstein n k x * gauge U (f k/ₙ - f x) :=
      (S.sum_add_sum_compl _).symm
    -- We'll now deal with the terms in `S` and the terms in `Sᶜ` in separate calc blocks.
    _ < 1 / 2 + 1 / 2 := add_lt_add_of_le_of_lt ?_ ?_
    _ = 1 := add_halves 1
  · -- We now work on the terms in `S`: uniform continuity and `bernstein.probability`
    -- quickly give us a bound.
    calc
      ∑ k in S, bernstein n k x * gauge U (f k/ₙ - f x) <= ∑ k in S, bernstein n k x * (1 / 2) := by
        gcongr with k hk
        refine (hδ _ _ ?_).le
        simpa [S] using hk
      _ = 1 / 2 * ∑ k in S, bernstein n k x := by rw [mul_comm, Finset.sum_mul]
      -- In this step we increase the sum over `S` back to a sum over all of `Fin (n+1)`,
      -- so that we can use `bernstein.probability`.
      _ <= 1 / 2 * ∑ k : Fin (n + 1), bernstein n k x := by gcongr; exact S.subset_univ
      _ = 1 / 2 := by rw [bernstein.probability, mul_one]
  · -- We now turn to working on `Sᶜ`: we control the difference term just using `C`,
    -- and then insert a `(x - k/n)^2 / δ^2` factor
    -- (which is at least one because we are not in `S`).
    calc
      ∑ k in Sᶜ, bernstein n k x * gauge U (f k/ₙ - f x) <= ∑ k in Sᶜ, C * bernstein n k x := by
        simp only [mul_comm (bernstein n _ x)]
        gcongr
        apply hC
      _ = C * ∑ k in Sᶜ, bernstein n k x := by rw [Finset.mul_sum]
      _ <= C * ∑ k in Sᶜ, ((x : Real) - k/ₙ) ^ 2 / δ ^ 2 * bernstein n k x := by
        gcongr with k hk
        conv_lhs => rw [← one_mul (bernstein _ _ _)]
        gcongr
        simpa [one_le_div₀, hδ₀, sq_le_sq, S, abs_of_pos, ← Real.dist_eq, dist_comm (x : Real)]
          using! hk
      -- Again enlarging the sum from `Sᶜ` to all of `Fin (n+1)`
      _ <= C * ∑ k : Fin (n + 1), ((x : Real) - k/ₙ) ^ 2 / δ ^ 2 * bernstein n k x := by
        gcongr; exact Sᶜ.subset_univ
      _ = C * (∑ k : Fin (n + 1), ((x : Real) - k/ₙ) ^ 2 * bernstein n k x) / δ ^ 2 := by
        simp only [← mul_div_right_comm, ← mul_div_assoc, ← Finset.sum_div]
      -- `bernstein.variance` and `x ∈ [0,1]` gives the uniform bound
      _ = C / δ ^ 2 * x * (1 - x) / n := by rw [variance hn₀]; ring
      _ <= C / δ ^ 2 * 1 * 1 / n := by gcongr <;> unit_interval
      _ < 1 / 2 := by simpa only [mul_one]
