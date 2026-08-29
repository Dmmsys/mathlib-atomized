/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Derivative is measurable

In this file we prove that the derivative of any function with complete codomain is a measurable
function. Namely, we prove:

* `measurableSet_of_differentiableAt`: the set `{x | DifferentiableAt 𝕜 f x}` is measurable;
* `measurable_fderiv`: the function `fderiv 𝕜 f` is measurable;
* `measurable_fderiv_apply_const`: for a fixed vector `y`, the function `fun x ↦ fderiv 𝕜 f x y`
  is measurable;
* `measurable_deriv`: the function `deriv f` is measurable (for `f : 𝕜 → F`).

We also show the same results for the right derivative on the real line
(see `measurable_derivWithin_Ici` and `measurable_derivWithin_Ioi`), following the same
proof strategy.

We also prove measurability statements for functions depending on a parameter: for `f : α → E → F`,
we show the measurability of `(p : α × E) ↦ fderiv 𝕜 (f p.1) p.2`. This requires additional
assumptions. We give versions of the above statements (appending `with_param` to their names) when
`f` is continuous and `E` is locally compact.

## Implementation

We give a proof that avoids second-countability issues, by expressing the differentiability set
as a function of open sets in the following way. Define `A (L, r, ε)` to be the set of points
where, on a ball of radius roughly `r` around `x`, the function is uniformly approximated by the
linear map `L`, up to `ε r`. It is an open set.
Let also `B (L, r, s, ε) = A (L, r, ε) ∩ A (L, s, ε)`: we require that at two possibly different
scales `r` and `s`, the function is well approximated by the linear map `L`. It is also open.

We claim that the differentiability set of `f` is exactly
`D = ⋂ ε > 0, ⋃ δ > 0, ⋂ r, s < δ, ⋃ L, B (L, r, s, ε)`.
In other words, for any `ε > 0`, we require that there is a size `δ` such that, for any two scales
below this size, the function is well approximated by a linear map, common to the two scales.

The set `⋃ L, B (L, r, s, ε)` is open, as a union of open sets. Converting the intersections and
unions to countable ones (using real numbers of the form `2 ^ (-n)`), it follows that the
differentiability set is measurable.

To prove the claim, there are two inclusions. One is trivial: if the function is differentiable
at `x`, then `x` belongs to `D` (just take `L` to be the derivative, and use that the
differentiability exactly says that the map is well approximated by `L`). This is proved in
`mem_A_of_differentiable` and `differentiable_set_subset_D`.

For the other direction, the difficulty is that `L` in the union may depend on `ε, r, s`. The key
point is that, in fact, it doesn't depend too much on them. First, if `x` belongs both to
`A (L, r, ε)` and `A (L', r, ε)`, then `L` and `L'` have to be close on a shell, and thus
`‖L - L'‖` is bounded by `ε` (see `norm_sub_le_of_mem_A`). Assume now `x ∈ D`. If one has two maps
`L` and `L'` such that `x` belongs to `A (L, r, ε)` and to `A (L', r', ε')`, one deduces that `L` is
close to `L'` by arguing as follows. Consider another scale `s` smaller than `r` and `r'`. Take a
linear map `L₁` that approximates `f` around `x` both at scales `r` and `s` w.r.t. `ε` (it exists as
`x` belongs to `D`). Take also `L₂` that approximates `f` around `x` both at scales `r'` and `s`
w.r.t. `ε'`. Then `L₁` is close to `L` (as they are close on a shell of radius `r`), and `L₂` is
close to `L₁` (as they are close on a shell of radius `s`), and `L'` is close to `L₂` (as they are
close on a shell of radius `r'`). It follows that `L` is close to `L'`, as we claimed.

It follows that the different approximating linear maps that show up form a Cauchy sequence when
`ε` tends to `0`. When the target space is complete, this sequence converges, to a limit `f'`.
With the same kind of arguments, one checks that `f` is differentiable with derivative `f'`.

To show that the derivative itself is measurable, add in the definition of `B` and `D` a set
`K` of continuous linear maps to which `L` should belong. Then, when `K` is complete, the set `D K`
is exactly the set of points where `f` is differentiable with a derivative in `K`.

## Tags

derivative, measurable function, Borel σ-algebra
-/

@[expose] public section


noncomputable section

open Set Metric Asymptotics Filter ContinuousLinearMap MeasureTheory TopologicalSpace
open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/--
theorem `measurable_apply₂` / 定理 `measurable_apply₂`

English:
theorem measurable_apply₂
  statement: [MeasurableSpace E] [OpensMeasurableSpace E]
  proof: isBoundedBilinearMap_apply.continuous.measurable

中文:
定理 measurable_apply₂
  结论: [MeasurableSpace E] [OpensMeasurableSpace E]
  证明: isBoundedBilinearMap_apply.continuous.measurable

Depends on / 依赖: continuous, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.continuous.measurable, measurable
-/
theorem measurable_apply₂ [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopologyEither (E ->L[𝕜] F) E]
    [MeasurableSpace F] [BorelSpace F] : Measurable fun p : (E ->L[𝕜] F) × E => p.1 p.2 :=
  isBoundedBilinearMap_apply.continuous.measurable

end ContinuousLinearMap

section fderiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E -> F} (K : Set (E ->L[𝕜] F))

namespace FDerivMeasurableAux

/--
Definition of `A` / `A` 的定义

English:
definition A
  signature: (f : E -> F) (L : E ->L[𝕜] F) (r ε : Real)
  body: { x | exists r' in Ioc (r / 2) r, forall y in ball x r', forall z in ball x r', ‖f z - f y - L (z - y)‖ < ε * r }

中文:
定义 A
  签名: (f : E -> F) (L : E ->L[𝕜] F) (r ε : 实数)
  定义体: { x | exists r' in Ioc (r / 2) r, forall y in ball x r', forall z in ball x r', ‖f z - f y - L (z - y)‖ < ε * r }
-/
def A (f : E -> F) (L : E ->L[𝕜] F) (r ε : Real) : Set E :=
  { x | exists r' in Ioc (r / 2) r, forall y in ball x r', forall z in ball x r', ‖f z - f y - L (z - y)‖ < ε * r }

/--
Definition of `B` / `B` 的定义

English:
definition B
  signature: (f : E -> F) (K : Set (E ->L[𝕜] F)) (r s ε : Real)
  body: ⋃ L in K, A f L r ε inter A f L s ε

中文:
定义 B
  签名: (f : E -> F) (K : Set (E ->L[𝕜] F)) (r s ε : 实数)
  定义体: ⋃ L in K, A f L r ε inter A f L s ε
-/
def B (f : E -> F) (K : Set (E ->L[𝕜] F)) (r s ε : Real) : Set E :=
  ⋃ L in K, A f L r ε inter A f L s ε

/--
Definition of `D` / `D` 的定义

English:
definition D
  signature: (f : E -> F) (K : Set (E ->L[𝕜] F))
  body: ⋂ e : Nat, ⋃ n : Nat, ⋂ (p >= n) (q >= n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)

中文:
定义 D
  签名: (f : E -> F) (K : Set (E ->L[𝕜] F))
  定义体: ⋂ e : Nat, ⋃ n : Nat, ⋂ (p >= n) (q >= n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)
-/
def D (f : E -> F) (K : Set (E ->L[𝕜] F)) : Set E :=
  ⋂ e : Nat, ⋃ n : Nat, ⋂ (p >= n) (q >= n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)

/--
theorem `isOpen_A` / 定理 `isOpen_A`

English:
theorem isOpen_A
  given: (L : E ->L[𝕜] F) (r ε : Real)
  statement: IsOpen (A f L r ε)
  proof: by
  rw [Metric.isOpen_iff]
  rintro x ⟨r', r'_mem, hr'⟩
  obtain ⟨s, s_gt, s_lt⟩ : exists s : Real, r / 2 < s ∧ s < r' := exists_between r'_mem.1
  have : s in Ioc (r / 2) r := ⟨s_gt, le_of_lt (s_lt.trans_le r'_mem.2)⟩
  refine ⟨r' - s, by linarith, fun x' hx' => ⟨s, this, ?_⟩⟩
  have B : ball x' s

中文:
定理 isOpen_A
  条件: (L : E ->L[𝕜] F) (r ε : 实数)
  结论: IsOpen (A f L r ε)
  证明: by
  rw [Metric.isOpen_iff]
  rintro x ⟨r', r'_mem, hr'⟩
  obtain ⟨s, s_gt, s_lt⟩ : exists s : Real, r / 2 < s ∧ s < r' := exists_between r'_mem.1
  have : s in Ioc (r / 2) r := ⟨s_gt, le_of_lt (s_lt.trans_le r'_mem.2)⟩
  refine ⟨r' - s, by linarith, fun x' hx' => ⟨s, this, ?_⟩⟩
  have B : ball x' s

Depends on / 依赖: Metric, Metric.isOpen_iff, _mem, ball_subset, exists_between, isOpen_iff, le_of_lt, s_gt, s_lt, s_lt.trans_le, subseteq, trans_le
-/
theorem isOpen_A (L : E ->L[𝕜] F) (r ε : Real) : IsOpen (A f L r ε) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨r', r'_mem, hr'⟩
  obtain ⟨s, s_gt, s_lt⟩ : exists s : Real, r / 2 < s ∧ s < r' := exists_between r'_mem.1
  have : s in Ioc (r / 2) r := ⟨s_gt, le_of_lt (s_lt.trans_le r'_mem.2)⟩
  refine ⟨r' - s, by linarith, fun x' hx' => ⟨s, this, ?_⟩⟩
  have B : ball x' s subseteq ball x r' := ball_subset (le_of_lt hx')
  intro y hy z hz
  exact hr' y (B hy) z (B hz)

/--
theorem `isOpen_B` / 定理 `isOpen_B`

English:
theorem isOpen_B
  given: {K : Set (E ->L[𝕜] F)} {r s ε : Real}
  statement: IsOpen (B f K r s ε)
  proof: by
  simp [B, isOpen_biUnion, IsOpen.inter, isOpen_A]

中文:
定理 isOpen_B
  条件: {K : Set (E ->L[𝕜] F)} {r s ε : 实数}
  结论: IsOpen (B f K r s ε)
  证明: by
  simp [B, isOpen_biUnion, IsOpen.inter, isOpen_A]

Depends on / 依赖: IsOpen, IsOpen.inter, isOpen_A, isOpen_biUnion
-/
theorem isOpen_B {K : Set (E ->L[𝕜] F)} {r s ε : Real} : IsOpen (B f K r s ε) := by
  simp [B, isOpen_biUnion, IsOpen.inter, isOpen_A]

/--
theorem `A_mono` / 定理 `A_mono`

English:
theorem A_mono
  given: (L : E ->L[𝕜] F) (r : Real) {ε δ : Real} (h : ε <= δ)
  statement: A f L r ε subseteq A f L r δ
  proof: by
  rintro x ⟨r', r'r, hr'⟩
  refine ⟨r', r'r, fun y hy z hz => (hr' y hy z hz).trans_le (mul_le_mul_of_nonneg_right h ?_)⟩
  linarith [mem_ball.1 hy, r'r.2, @dist_nonneg _ _ y x]

中文:
定理 A_mono
  条件: (L : E ->L[𝕜] F) (r : 实数) {ε δ : 实数} (h : ε <= δ)
  结论: A f L r ε subseteq A f L r δ
  证明: by
  rintro x ⟨r', r'r, hr'⟩
  refine ⟨r', r'r, fun y hy z hz => (hr' y hy z hz).trans_le (mul_le_mul_of_nonneg_right h ?_)⟩
  linarith [mem_ball.1 hy, r'r.2, @dist_nonneg _ _ y x]

Depends on / 依赖: dist_nonneg, mem_ball, mul_le_mul_of_nonneg_right, trans_le
-/
theorem A_mono (L : E ->L[𝕜] F) (r : Real) {ε δ : Real} (h : ε <= δ) : A f L r ε subseteq A f L r δ := by
  rintro x ⟨r', r'r, hr'⟩
  refine ⟨r', r'r, fun y hy z hz => (hr' y hy z hz).trans_le (mul_le_mul_of_nonneg_right h ?_)⟩
  linarith [mem_ball.1 hy, r'r.2, @dist_nonneg _ _ y x]

/--
theorem `le_of_mem_A` / 定理 `le_of_mem_A`

English:
theorem le_of_mem_A
  statement: {r ε : Real} {L : E ->L[𝕜] F} {x : E} (hx : x in A f L r ε) {y z : E}
  proof: by
  rcases hx with ⟨r', r'mem, hr'⟩
  apply le_of_lt
  exact hr' _ ((mem_closedBall.1 hy).trans_lt r'mem.1) _ ((mem_closedBall.1 hz).trans_lt r'mem.1)

中文:
定理 le_of_mem_A
  结论: {r ε : 实数} {L : E ->L[𝕜] F} {x : E} (hx : x in A f L r ε) {y z : E}
  证明: by
  rcases hx with ⟨r', r'mem, hr'⟩
  apply le_of_lt
  exact hr' _ ((mem_closedBall.1 hy).trans_lt r'mem.1) _ ((mem_closedBall.1 hz).trans_lt r'mem.1)

Depends on / 依赖: le_of_lt, mem_closedBall, trans_lt
-/
theorem le_of_mem_A {r ε : Real} {L : E ->L[𝕜] F} {x : E} (hx : x in A f L r ε) {y z : E}
    (hy : y in closedBall x (r / 2)) (hz : z in closedBall x (r / 2)) :
    ‖f z - f y - L (z - y)‖ <= ε * r := by
  rcases hx with ⟨r', r'mem, hr'⟩
  apply le_of_lt
  exact hr' _ ((mem_closedBall.1 hy).trans_lt r'mem.1) _ ((mem_closedBall.1 hz).trans_lt r'mem.1)

/--
theorem `mem_A_of_differentiable` / 定理 `mem_A_of_differentiable`

English:
theorem mem_A_of_differentiable
  given: {ε : Real} (hε : 0 < ε) {x : E} (hx : DifferentiableAt 𝕜 f x)
  proof: by
  let δ := (ε / 2) / 2
  obtain ⟨R, R_pos, hR⟩ :
      exists R > 0, forall y in ball x R, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ <= δ * ‖y - x‖ :=
eventually_nhds_iff_ball.1 hx.hasFDerivAt.isLittleO.bound by positivity
  refine ⟨R, R_pos, fun r hr => ?_⟩
have : r in Ioc (r / 2) r := right_mem_Ioc.2 

中文:
定理 mem_A_of_differentiable
  条件: {ε : 实数} (hε : 0 < ε) {x : E} (hx : DifferentiableAt 𝕜 f x)
  证明: by
  let δ := (ε / 2) / 2
  obtain ⟨R, R_pos, hR⟩ :
      exists R > 0, forall y in ball x R, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ <= δ * ‖y - x‖ :=
eventually_nhds_iff_ball.1 hx.hasFDerivAt.isLittleO.bound by positivity
  refine ⟨R, R_pos, fun r hr => ?_⟩
have : r in Ioc (r / 2) r := right_mem_Ioc.2 

Depends on / 依赖: R_pos, abel_nf, eventually_nhds_iff_ball, fderiv, half_lt_self, hasFDerivAt, hx.hasFDerivAt.isLittleO.bound, isLittleO, map_sub, right_mem_Ioc
-/
theorem mem_A_of_differentiable {ε : Real} (hε : 0 < ε) {x : E} (hx : DifferentiableAt 𝕜 f x) :
    exists R > 0, forall r in Ioo (0 : Real) R, x in A f (fderiv 𝕜 f x) r ε := by
  let δ := (ε / 2) / 2
  obtain ⟨R, R_pos, hR⟩ :
      exists R > 0, forall y in ball x R, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ <= δ * ‖y - x‖ :=
eventually_nhds_iff_ball.1 hx.hasFDerivAt.isLittleO.bound by positivity
  refine ⟨R, R_pos, fun r hr => ?_⟩
have : r in Ioc (r / 2) r := right_mem_Ioc.2 half_lt_self hr.1
  refine ⟨r, this, fun y hy z hz => ?_⟩
  calc
    ‖f z - f y - (fderiv 𝕜 f x) (z - y)‖ =
        ‖f z - f x - (fderiv 𝕜 f x) (z - x) - (f y - f x - (fderiv 𝕜 f x) (y - x))‖ := by
      simp only [map_sub]; abel_nf
    _ <= ‖f z - f x - (fderiv 𝕜 f x) (z - x)‖ + ‖f y - f x - (fderiv 𝕜 f x) (y - x)‖ :=
      norm_sub_le _ _
    _ <= δ * ‖z - x‖ + δ * ‖y - x‖ :=
      add_le_add (hR _ (ball_subset_ball hr.2.le hz)) (hR _ (ball_subset_ball hr.2.le hy))
    _ <= δ * r + δ * r := by rw [mem_ball_iff_norm] at hz hy; gcongr
    _ = (ε / 2) * r := by ring
    _ < ε * r := by gcongr; exacts [hr.1, half_lt_self hε]

/--
theorem `norm_sub_le_of_mem_A` / 定理 `norm_sub_le_of_mem_A`

English:
theorem norm_sub_le_of_mem_A
  statement: {c : 𝕜} (hc : 1 < ‖c‖) {r ε : Real} (hε : 0 < ε) (hr : 0 < r) {x : E}
  proof: by
  refine opNorm_le_of_shell (half_pos hr) (by positivity) hc ?_
  intro y ley ylt
  rw [div_div]; rw [div_le_iff₀' (by positivity)] at ley
  calc
    ‖(L₁ - L₂) y‖ = ‖f (x + y) - f x - L₂ (x + y - x) - (f (x + y) - f x - L₁ (x + y - x))‖ := by
      simp
    _ <= ‖f (x + y) - f x - L₂ (x + y - x)

中文:
定理 norm_sub_le_of_mem_A
  结论: {c : 𝕜} (hc : 1 < ‖c‖) {r ε : 实数} (hε : 0 < ε) (hr : 0 < r) {x : E}
  证明: by
  refine opNorm_le_of_shell (half_pos hr) (by positivity) hc ?_
  intro y ley ylt
  rw [div_div]; rw [div_le_iff₀' (by positivity)] at ley
  calc
    ‖(L₁ - L₂) y‖ = ‖f (x + y) - f x - L₂ (x + y - x) - (f (x + y) - f x - L₁ (x + y - x))‖ := by
      simp
    _ <= ‖f (x + y) - f x - L₂ (x + y - x)

Depends on / 依赖: add_le_add, add_sub_, dist_eq_norm, dist_self, div_div, half_pos, le_of_lt, le_of_mem_A, mem_closedBall, norm_sub_le, opNorm_le_of_shell
-/
theorem norm_sub_le_of_mem_A {c : 𝕜} (hc : 1 < ‖c‖) {r ε : Real} (hε : 0 < ε) (hr : 0 < r) {x : E}
    {L₁ L₂ : E ->L[𝕜] F} (h₁ : x in A f L₁ r ε) (h₂ : x in A f L₂ r ε) : ‖L₁ - L₂‖ <= 4 * ‖c‖ * ε := by
  refine opNorm_le_of_shell (half_pos hr) (by positivity) hc ?_
  intro y ley ylt
  rw [div_div]; rw [div_le_iff₀' (by positivity)] at ley
  calc
    ‖(L₁ - L₂) y‖ = ‖f (x + y) - f x - L₂ (x + y - x) - (f (x + y) - f x - L₁ (x + y - x))‖ := by
      simp
    _ <= ‖f (x + y) - f x - L₂ (x + y - x)‖ + ‖f (x + y) - f x - L₁ (x + y - x)‖ := norm_sub_le _ _
    _ <= ε * r + ε * r := by
      apply add_le_add
      · apply le_of_mem_A h₂
        · simp only [le_of_lt (half_pos hr), mem_closedBall, dist_self]
        · simp only [dist_eq_norm, add_sub_cancel_left, mem_closedBall, ylt.le]
      · apply le_of_mem_A h₁
        · simp only [le_of_lt (half_pos hr), mem_closedBall, dist_self]
        · simp only [dist_eq_norm, add_sub_cancel_left, mem_closedBall, ylt.le]
    _ = 2 * ε * r := by ring
    _ <= 2 * ε * (2 * ‖c‖ * ‖y‖) := by gcongr
    _ = 4 * ‖c‖ * ε * ‖y‖ := by ring

/--
theorem `differentiable_set_subset_D` / 定理 `differentiable_set_subset_D`

English:
theorem differentiable_set_subset_D
  proof: by
  intro x hx
  rw [D]; rw [mem_iInter]
  intro e
  have : (0 : Real) < (1 / 2) ^ e := by positivity
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩
  obtain ⟨n, hn⟩ : exists n : Nat, (1 / 2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : Real) / 2 < 1)
  simp only

中文:
定理 differentiable_set_subset_D
  证明: by
  intro x hx
  rw [D]; rw [mem_iInter]
  intro e
  have : (0 : Real) < (1 / 2) ^ e := by positivity
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩
  obtain ⟨n, hn⟩ : exists n : Nat, (1 / 2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : Real) / 2 < 1)
  simp only

Depends on / 依赖: R_pos, exists_pow_lt_of_lt_one, fderiv, lt_of_le_of_lt, mem_A_of_differentiable, mem_iInter, mem_iUnion, mem_inter_iff, pow_le_pow_of_le_one
-/
theorem differentiable_set_subset_D :
    { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in K } subseteq D f K := by
  intro x hx
  rw [D]; rw [mem_iInter]
  intro e
  have : (0 : Real) < (1 / 2) ^ e := by positivity
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩
  obtain ⟨n, hn⟩ : exists n : Nat, (1 / 2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : Real) / 2 < 1)
  simp only [mem_iUnion, mem_iInter, B, mem_inter_iff]
  refine ⟨n, fun p hp q hq => ⟨fderiv 𝕜 f x, hx.2, ⟨?_, ?_⟩⟩⟩ <;>
    · refine hR _ ⟨by positivity, lt_of_le_of_lt ?_ hn⟩
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by assumption)

/--
theorem `D_subset_differentiable_set` / 定理 `D_subset_differentiable_set`

English:
theorem D_subset_differentiable_set
  given: {K : Set (E ->L[𝕜] F)} (hK : IsComplete K)
  proof: by
  have P : forall {n : Nat}, (0 : Real) < (1 / 2) ^ n := fun {n} => pow_pos (by norm_num) n
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  intro x hx
  have :
    forall e : Nat, exists n : Nat, forall p q, n <= p -> n <= q ->
      exists L in K, x in A f L ((1 / 2) ^ p) ((1 / 2) ^ e) 

中文:
定理 D_subset_differentiable_set
  条件: {K : Set (E ->L[𝕜] F)} (hK : IsComplete K)
  证明: by
  have P : forall {n : Nat}, (0 : Real) < (1 / 2) ^ n := fun {n} => pow_pos (by norm_num) n
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  intro x hx
  have :
    forall e : Nat, exists n : Nat, forall p q, n <= p -> n <= q ->
      exists L in K, x in A f L ((1 / 2) ^ p) ((1 / 2) ^ e) 

Depends on / 依赖: NormedField, NormedField.exists_one_lt_norm, exists_one_lt_norm, mem_iInter, mem_iUnion, pow_pos
-/
theorem D_subset_differentiable_set {K : Set (E ->L[𝕜] F)} (hK : IsComplete K) :
    D f K subseteq { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in K } := by
  have P : forall {n : Nat}, (0 : Real) < (1 / 2) ^ n := fun {n} => pow_pos (by norm_num) n
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  intro x hx
  have :
    forall e : Nat, exists n : Nat, forall p q, n <= p -> n <= q ->
      exists L in K, x in A f L ((1 / 2) ^ p) ((1 / 2) ^ e) inter A f L ((1 / 2) ^ q) ((1 / 2) ^ e) := by
    intro e
    have := mem_iInter.1 hx e
    rcases mem_iUnion.1 this with ⟨n, hn⟩
    refine ⟨n, fun p q hp hq => ?_⟩
    simp only [mem_iInter] at hn
    rcases mem_iUnion.1 (hn p hp q hq) with ⟨L, hL⟩
exact ⟨L, exists_prop.mp mem_iUnion.1 hL⟩
  /- Recast the assumptions: for each `e`, there exist `n e` and linear maps `L e p q` in `K`
    such that, for `p, q ≥ n e`, then `f` is well approximated by `L e p q` at scale `2 ^ (-p)` and
    `2 ^ (-q)`, with an error `2 ^ (-e)`. -/
  choose! n L hn using this
  /- All the operators `L e p q` that show up are close to each other. To prove this, we argue
      that `L e p q` is close to `L e p r` (where `r` is large enough), as both approximate `f` at
      scale `2 ^(- p)`. And `L e p r` is close to `L e' p' r` as both approximate `f` at scale
      `2 ^ (- r)`. And `L e' p' r` is close to `L e' p' q'` as both approximate `f` at scale
      `2 ^ (- p')`. -/
  have M :
    forall e p q e' p' q',
      n e <= p ->
        n e <= q ->
          n e' <= p' -> n e' <= q' -> e <= e' -> ‖L e p q - L e' p' q'‖ <= 12 * ‖c‖ * (1 / 2) ^ e := by
    intro e p q e' p' q' hp hq hp' hq' he'
    let r := max (n e) (n e')
    have I : ((1 : Real) / 2) ^ e' <= (1 / 2) ^ e :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) he'
    have J1 : ‖L e p q - L e p r‖ <= 4 * ‖c‖ * (1 / 2) ^ e := by
      have I1 : x in A f (L e p q) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p q hp hq).2.1
      have I2 : x in A f (L e p r) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p r hp (le_max_left _ _)).2.1
      exact norm_sub_le_of_mem_A hc P P I1 I2
    have J2 : ‖L e p r - L e' p' r‖ <= 4 * ‖c‖ * (1 / 2) ^ e := by
      have I1 : x in A f (L e p r) ((1 / 2) ^ r) ((1 / 2) ^ e) := (hn e p r hp (le_max_left _ _)).2.2
      have I2 : x in A f (L e' p' r) ((1 / 2) ^ r) ((1 / 2) ^ e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.2
      exact norm_sub_le_of_mem_A hc P P I1 (A_mono _ _ I I2)
    have J3 : ‖L e' p' r - L e' p' q'‖ <= 4 * ‖c‖ * (1 / 2) ^ e := by
      have I1 : x in A f (L e' p' r) ((1 / 2) ^ p') ((1 / 2) ^ e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.1
      have I2 : x in A f (L e' p' q') ((1 / 2) ^ p') ((1 / 2) ^ e') := (hn e' p' q' hp' hq').2.1
      exact norm_sub_le_of_mem_A hc P P (A_mono _ _ I I1) (A_mono _ _ I I2)
    calc
      ‖L e p q - L e' p' q'‖ =
          ‖L e p q - L e p r + (L e p r - L e' p' r) + (L e' p' r - L e' p' q')‖ := by
        congr 1; abel
      _ <= ‖L e p q - L e p r‖ + ‖L e p r - L e' p' r‖ + ‖L e' p' r - L e' p' q'‖ :=
        norm_add₃_le
      _ <= 4 * ‖c‖ * (1 / 2) ^ e + 4 * ‖c‖ * (1 / 2) ^ e + 4 * ‖c‖ * (1 / 2) ^ e := by gcongr
      _ = 12 * ‖c‖ * (1 / 2) ^ e := by ring
  /- For definiteness, use `L0 e = L e (n e) (n e)`, to have a single sequence. We claim that this
    is a Cauchy sequence. -/
  let L0 : Nat -> E ->L[𝕜] F := fun e => L e (n e) (n e)
  have : CauchySeq L0 := by
    rw [Metric.cauchySeq_iff']
    intro ε εpos
    obtain ⟨e, he⟩ : exists e : Nat, (1 / 2) ^ e < ε / (12 * ‖c‖) :=
      exists_pow_lt_of_lt_one (by positivity) (by norm_num)
    refine ⟨e, fun e' he' => ?_⟩
    rw [dist_comm]; rw [dist_eq_norm]
    calc
      ‖L0 e - L0 e'‖ <= 12 * ‖c‖ * (1 / 2) ^ e := M _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl he'
      _ < 12 * ‖c‖ * (ε / (12 * ‖c‖)) := by gcongr
      _ = ε := by field
  -- As it is Cauchy, the sequence `L0` converges, to a limit `f'` in `K`.
  obtain ⟨f', f'K, hf'⟩ : exists f' in K, Tendsto L0 atTop (𝓝 f') :=
    cauchySeq_tendsto_of_isComplete hK (fun e => (hn e (n e) (n e) le_rfl le_rfl).1) this
  have Lf' : forall e p, n e <= p -> ‖L e (n e) p - f'‖ <= 12 * ‖c‖ * (1 / 2) ^ e := by
    intro e p hp
    apply le_of_tendsto (tendsto_const_nhds.sub hf').norm
    rw [eventually_atTop]
    exact ⟨e, fun e' he' => M _ _ _ _ _ _ le_rfl hp le_rfl le_rfl he'⟩
  -- Let us show that `f` has derivative `f'` at `x`.
  have : HasFDerivAt f f' x := by
    simp only [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
    /- to get an approximation with a precision `ε`, we will replace `f` with `L e (n e) m` for
      some large enough `e` (yielding a small error by uniform approximation). As one can vary `m`,
      this makes it possible to cover all scales, and thus to obtain a good linear approximation in
      the whole ball of radius `(1/2)^(n e)`. -/
    intro ε εpos
    have pos : 0 < 4 + 12 * ‖c‖ := by positivity
    obtain ⟨e, he⟩ : exists e : Nat, (1 / 2) ^ e < ε / (4 + 12 * ‖c‖) :=
      exists_pow_lt_of_lt_one (div_pos εpos pos) (by norm_num)
    rw [eventually_nhds_iff_ball]
    refine ⟨(1 / 2) ^ (n e + 1), P, fun y hy => ?_⟩
    -- We need to show that `f (x + y) - f x - f' y` is small. For this, we will work at scale
    -- `k` where `k` is chosen with `‖y‖ ∼ 2 ^ (-k)`.
    by_cases y_pos : y = 0
    · simp [y_pos]
    have yzero : 0 < ‖y‖ := norm_pos_iff.mpr y_pos
    have y_lt : ‖y‖ < (1 / 2) ^ (n e + 1) := by simpa using mem_ball_iff_norm.1 hy
    have yone : ‖y‖ <= 1 := le_trans y_lt.le (pow_le_one₀ (by norm_num) (by norm_num))
    -- define the scale `k`.
    obtain ⟨k, hk, h'k⟩ : exists k : Nat, (1 / 2) ^ (k + 1) < ‖y‖ ∧ ‖y‖ <= (1 / 2) ^ k :=
      exists_nat_pow_near_of_lt_one yzero yone (by norm_num : (0 : Real) < 1 / 2)
        (by norm_num : (1 : Real) / 2 < 1)
    -- the scale is large enough (as `y` is small enough)
    have k_gt : n e < k := by
      have : ((1 : Real) / 2) ^ (k + 1) < (1 / 2) ^ (n e + 1) := lt_trans hk y_lt
      rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : Real) < 1 / 2) (by norm_num)] at this
      lia
    set m := k - 1
    have m_ge : n e <= m := Nat.le_sub_one_of_lt k_gt
    have km : k = m + 1 := (Nat.succ_pred_eq_of_pos k_gt.pos).symm
    rw [km] at hk h'k
    -- `f` is well approximated by `L e (n e) k` at the relevant scale
    -- (in fact, we use `m = k - 1` instead of `k` because of the precise definition of `A`).
    have J1 : ‖f (x + y) - f x - L e (n e) m (x + y - x)‖ <= (1 / 2) ^ e * (1 / 2) ^ m := by
      apply le_of_mem_A (hn e (n e) m le_rfl m_ge).2.2
      · simp only [mem_closedBall, dist_self]
        positivity
      · simpa only [dist_eq_norm, add_sub_cancel_left, mem_closedBall, pow_succ, mul_one_div] using
          h'k
    have J2 : ‖f (x + y) - f x - L e (n e) m y‖ <= 4 * (1 / 2) ^ e * ‖y‖ :=
      calc
        ‖f (x + y) - f x - L e (n e) m y‖ <= (1 / 2) ^ e * (1 / 2) ^ m := by
          simpa only [add_sub_cancel_left] using J1
        _ = 4 * (1 / 2) ^ e * (1 / 2) ^ (m + 2) := by ring
        _ <= 4 * (1 / 2) ^ e * ‖y‖ := by gcongr
    -- use the previous estimates to see that `f (x + y) - f x - f' y` is small.
    calc
      ‖f (x + y) - f x - f' y‖ = ‖f (x + y) - f x - L e (n e) m y + (L e (n e) m - f') y‖ :=
        congr_arg _ (by simp)
      _ <= 4 * (1 / 2) ^ e * ‖y‖ + 12 * ‖c‖ * (1 / 2) ^ e * ‖y‖ :=
norm_add_le_of_le J2 (le_opNorm _ _).trans by gcongr; exact Lf' _ _ m_ge
      _ = (4 + 12 * ‖c‖) * ‖y‖ * (1 / 2) ^ e := by ring
      _ <= (4 + 12 * ‖c‖) * ‖y‖ * (ε / (4 + 12 * ‖c‖)) := by gcongr
      _ = ε * ‖y‖ := by field
  rw [← this.fderiv] at f'K
  exact ⟨this.differentiableAt, f'K⟩

/--
theorem `differentiable_set_eq_D` / 定理 `differentiable_set_eq_D`

English:
theorem differentiable_set_eq_D
  given: (hK : IsComplete K)
  proof: Subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

中文:
定理 differentiable_set_eq_D
  条件: (hK : IsComplete K)
  证明: Subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

Depends on / 依赖: D_subset_differentiable_set, Subset, Subset.antisymm, antisymm, differentiable_set_subset_D
-/
theorem differentiable_set_eq_D (hK : IsComplete K) :
    { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in K } = D f K :=
  Subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

end FDerivMeasurableAux

open FDerivMeasurableAux

variable [MeasurableSpace E] [OpensMeasurableSpace E]
variable (𝕜 f)

/--
theorem `measurableSet_of_differentiableAt_of_isComplete` / 定理 `measurableSet_of_differentiableAt_of_isComplete`

English:
theorem measurableSet_of_differentiableAt_of_isComplete
  given: {K : Set (E ->L[𝕜] F)} (hK : IsComplete K)
  proof: by
  simp only [D, differentiable_set_eq_D K hK]
  aesop
    (add safe apply [MeasurableSet.iUnion, MeasurableSet.iInter, isOpen_B])
    (add unsafe IsOpen.measurableSet)

中文:
定理 measurableSet_of_differentiableAt_of_isComplete
  条件: {K : Set (E ->L[𝕜] F)} (hK : IsComplete K)
  证明: by
  simp only [D, differentiable_set_eq_D K hK]
  aesop
    (add safe apply [MeasurableSet.iUnion, MeasurableSet.iInter, isOpen_B])
    (add unsafe IsOpen.measurableSet)

Depends on / 依赖: IsOpen, IsOpen.measurableSet, MeasurableSet, MeasurableSet.iInter, MeasurableSet.iUnion, differentiable_set_eq_D, iInter, iUnion, isOpen_B, measurableSet, unsafe
-/
theorem measurableSet_of_differentiableAt_of_isComplete {K : Set (E ->L[𝕜] F)} (hK : IsComplete K) :
    MeasurableSet { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in K } := by
  simp only [D, differentiable_set_eq_D K hK]
  aesop
    (add safe apply [MeasurableSet.iUnion, MeasurableSet.iInter, isOpen_B])
    (add unsafe IsOpen.measurableSet)

variable [CompleteSpace F]

/--
theorem `measurableSet_of_differentiableAt` / 定理 `measurableSet_of_differentiableAt`

English:
theorem measurableSet_of_differentiableAt
  statement: MeasurableSet { x | DifferentiableAt 𝕜 f x }
  proof: by
  have : IsComplete (univ : Set (E ->L[𝕜] F)) := isComplete_univ
  convert! measurableSet_of_differentiableAt_of_isComplete 𝕜 f this
  simp

@[fun_prop]

中文:
定理 measurableSet_of_differentiableAt
  结论: MeasurableSet { x | DifferentiableAt 𝕜 f x }
  证明: by
  have : IsComplete (univ : Set (E ->L[𝕜] F)) := isComplete_univ
  convert! measurableSet_of_differentiableAt_of_isComplete 𝕜 f this
  simp

@[fun_prop]

Depends on / 依赖: IsComplete, convert, isComplete_univ, measurableSet_of_differentiableAt_of_isComplete
-/
theorem measurableSet_of_differentiableAt : MeasurableSet { x | DifferentiableAt 𝕜 f x } := by
  have : IsComplete (univ : Set (E ->L[𝕜] F)) := isComplete_univ
  convert! measurableSet_of_differentiableAt_of_isComplete 𝕜 f this
  simp

@[fun_prop]
/--
theorem `measurable_fderiv` / 定理 `measurable_fderiv`

English:
theorem measurable_fderiv
  statement: Measurable (fderiv 𝕜 f)
  proof: by
  refine measurable_of_isClosed fun s hs => ?_
  have :
    fderiv 𝕜 f ⁻¹' s =
      { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in s } union
        { x | ¬DifferentiableAt 𝕜 f x } inter { _x | (0 : E ->L[𝕜] F) in s } :=
    Set.ext fun x => mem_preimage.trans fderiv_mem_iff
  rw [this]
  exact


中文:
定理 measurable_fderiv
  结论: Measurable (fderiv 𝕜 f)
  证明: by
  refine measurable_of_isClosed fun s hs => ?_
  have :
    fderiv 𝕜 f ⁻¹' s =
      { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in s } union
        { x | ¬DifferentiableAt 𝕜 f x } inter { _x | (0 : E ->L[𝕜] F) in s } :=
    Set.ext fun x => mem_preimage.trans fderiv_mem_iff
  rw [this]
  exact


Depends on / 依赖: DifferentiableAt, MeasurableSet, MeasurableSet.const, Set.ext, compl.inter, fderiv, fderiv_mem_iff, hs.isComplete, isComplete, measurableSet_of_differentiableAt, measurableSet_of_differentiableAt_of_isComplete, measurable_of_isClosed, mem_preimage, mem_preimage.trans
-/
theorem measurable_fderiv : Measurable (fderiv 𝕜 f) := by
  refine measurable_of_isClosed fun s hs => ?_
  have :
    fderiv 𝕜 f ⁻¹' s =
      { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in s } union
        { x | ¬DifferentiableAt 𝕜 f x } inter { _x | (0 : E ->L[𝕜] F) in s } :=
    Set.ext fun x => mem_preimage.trans fderiv_mem_iff
  rw [this]
  exact
    (measurableSet_of_differentiableAt_of_isComplete _ _ hs.isComplete).union
      ((measurableSet_of_differentiableAt _ _).compl.inter (MeasurableSet.const _))

@[fun_prop]
/--
theorem `measurable_fderiv_apply_const` / 定理 `measurable_fderiv_apply_const`

English:
theorem measurable_fderiv_apply_const
  given: [MeasurableSpace F] [BorelSpace F] (y : E)
  proof: (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv 𝕜 f)

中文:
定理 measurable_fderiv_apply_const
  条件: [MeasurableSpace F] [BorelSpace F] (y : E)
  证明: (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv 𝕜 f)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.measurable_apply, measurable_apply, measurable_fderiv
-/
theorem measurable_fderiv_apply_const [MeasurableSpace F] [BorelSpace F] (y : E) :
    Measurable fun x => fderiv 𝕜 f x y :=
  (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv 𝕜 f)

variable {𝕜}

@[fun_prop]
/--
theorem `measurable_deriv` / 定理 `measurable_deriv`

English:
theorem measurable_deriv
  statement: [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
  proof: by
  simpa only [fderiv_apply_one_eq_deriv] using measurable_fderiv_apply_const 𝕜 f 1

中文:
定理 measurable_deriv
  结论: [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
  证明: by
  simpa only [fderiv_apply_one_eq_deriv] using measurable_fderiv_apply_const 𝕜 f 1

Depends on / 依赖: fderiv_apply_one_eq_deriv, measurable_fderiv_apply_const
-/
theorem measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] (f : 𝕜 -> F) : Measurable (deriv f) := by
  simpa only [fderiv_apply_one_eq_deriv] using measurable_fderiv_apply_const 𝕜 f 1

/--
theorem `stronglyMeasurable_deriv` / 定理 `stronglyMeasurable_deriv`

English:
theorem stronglyMeasurable_deriv
  statement: [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
  proof: by
  borelize F
  rcases h.out with h𝕜 | hF
  · exact stronglyMeasurable_iff_measurable_separable.2
      ⟨measurable_deriv f, isSeparable_range_deriv _⟩
  · exact (measurable_deriv f).stronglyMeasurable

中文:
定理 stronglyMeasurable_deriv
  结论: [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
  证明: by
  borelize F
  rcases h.out with h𝕜 | hF
  · exact stronglyMeasurable_iff_measurable_separable.2
      ⟨measurable_deriv f, isSeparable_range_deriv _⟩
  · exact (measurable_deriv f).stronglyMeasurable

Depends on / 依赖: borelize, h.out, isSeparable_range_deriv, measurable_deriv, stronglyMeasurable, stronglyMeasurable_iff_measurable_separable
-/
theorem stronglyMeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [h : SecondCountableTopologyEither 𝕜 F] (f : 𝕜 -> F) : StronglyMeasurable (deriv f) := by
  borelize F
  rcases h.out with h𝕜 | hF
  · exact stronglyMeasurable_iff_measurable_separable.2
      ⟨measurable_deriv f, isSeparable_range_deriv _⟩
  · exact (measurable_deriv f).stronglyMeasurable

/--
theorem `aemeasurable_deriv` / 定理 `aemeasurable_deriv`

English:
theorem aemeasurable_deriv
  statement: [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
  proof: (measurable_deriv f).aemeasurable

中文:
定理 aemeasurable_deriv
  结论: [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
  证明: (measurable_deriv f).aemeasurable

Depends on / 依赖: aemeasurable, measurable_deriv
-/
theorem aemeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] (f : 𝕜 -> F) (μ : Measure 𝕜) : AEMeasurable (deriv f) μ :=
  (measurable_deriv f).aemeasurable

/--
theorem `aestronglyMeasurable_deriv` / 定理 `aestronglyMeasurable_deriv`

English:
theorem aestronglyMeasurable_deriv
  statement: [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
  proof: (stronglyMeasurable_deriv f).aestronglyMeasurable

中文:
定理 aestronglyMeasurable_deriv
  结论: [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
  证明: (stronglyMeasurable_deriv f).aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, stronglyMeasurable_deriv
-/
theorem aestronglyMeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [SecondCountableTopologyEither 𝕜 F] (f : 𝕜 -> F) (μ : Measure 𝕜) :
    AEStronglyMeasurable (deriv f) μ :=
  (stronglyMeasurable_deriv f).aestronglyMeasurable

end fderiv

section RightDeriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {f : Real -> F} (K : Set F)

namespace RightDerivMeasurableAux

/--
Definition of `A` / `A` 的定义

English:
definition A
  signature: (f : Real -> F) (L : F) (r ε : Real)
  body: { x | exists r' in Ioc (r / 2) r, forallᵉ (y in Icc x (x + r')) (z in Icc x (x + r')),
    ‖f z - f y - (z - y) • L‖ <= ε * r }

中文:
定义 A
  签名: (f : 实数 -> F) (L : F) (r ε : 实数)
  定义体: { x | exists r' in Ioc (r / 2) r, forallᵉ (y in Icc x (x + r')) (z in Icc x (x + r')),
    ‖f z - f y - (z - y) • L‖ <= ε * r }
-/
def A (f : Real -> F) (L : F) (r ε : Real) : Set Real :=
  { x | exists r' in Ioc (r / 2) r, forallᵉ (y in Icc x (x + r')) (z in Icc x (x + r')),
    ‖f z - f y - (z - y) • L‖ <= ε * r }

/--
Definition of `B` / `B` 的定义

English:
definition B
  signature: (f : Real -> F) (K : Set F) (r s ε : Real)
  body: ⋃ L in K, A f L r ε inter A f L s ε

中文:
定义 B
  签名: (f : 实数 -> F) (K : Set F) (r s ε : 实数)
  定义体: ⋃ L in K, A f L r ε inter A f L s ε
-/
def B (f : Real -> F) (K : Set F) (r s ε : Real) : Set Real :=
  ⋃ L in K, A f L r ε inter A f L s ε

/--
Definition of `D` / `D` 的定义

English:
definition D
  signature: (f : Real -> F) (K : Set F)
  body: ⋂ e : Nat, ⋃ n : Nat, ⋂ (p >= n) (q >= n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)

中文:
定义 D
  签名: (f : 实数 -> F) (K : Set F)
  定义体: ⋂ e : Nat, ⋃ n : Nat, ⋂ (p >= n) (q >= n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)
-/
def D (f : Real -> F) (K : Set F) : Set Real :=
  ⋂ e : Nat, ⋃ n : Nat, ⋂ (p >= n) (q >= n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)

/--
theorem `A_mem_nhdsGT` / 定理 `A_mem_nhdsGT`

English:
theorem A_mem_nhdsGT
  given: {L : F} {r ε x : Real} (hx : x in A f L r ε)
  statement: A f L r ε in 𝓝[>] x
  proof: by
  rcases hx with ⟨r', rr', hr'⟩
  obtain ⟨s, s_gt, s_lt⟩ : exists s : Real, r / 2 < s ∧ s < r' := exists_between rr'.1
  have : s in Ioc (r / 2) r := ⟨s_gt, le_of_lt (s_lt.trans_le rr'.2)⟩
  filter_upwards [Ioo_mem_nhdsGT <| show x < x + r' - s by linarith] with x' hx'
  use s, this
  have A : Ic

中文:
定理 A_mem_nhdsGT
  条件: {L : F} {r ε x : 实数} (hx : x in A f L r ε)
  结论: A f L r ε in 𝓝[>] x
  证明: by
  rcases hx with ⟨r', rr', hr'⟩
  obtain ⟨s, s_gt, s_lt⟩ : exists s : Real, r / 2 < s ∧ s < r' := exists_between rr'.1
  have : s in Ioc (r / 2) r := ⟨s_gt, le_of_lt (s_lt.trans_le rr'.2)⟩
  filter_upwards [Ioo_mem_nhdsGT <| show x < x + r' - s by linarith] with x' hx'
  use s, this
  have A : Ic

Depends on / 依赖: Icc_subset_Icc, Ioo_mem_nhdsGT, exists_between, filter_upwards, le_of_lt, s_gt, s_lt, s_lt.trans_le, subseteq, trans_le
-/
theorem A_mem_nhdsGT {L : F} {r ε x : Real} (hx : x in A f L r ε) : A f L r ε in 𝓝[>] x := by
  rcases hx with ⟨r', rr', hr'⟩
  obtain ⟨s, s_gt, s_lt⟩ : exists s : Real, r / 2 < s ∧ s < r' := exists_between rr'.1
  have : s in Ioc (r / 2) r := ⟨s_gt, le_of_lt (s_lt.trans_le rr'.2)⟩
  filter_upwards [Ioo_mem_nhdsGT <| show x < x + r' - s by linarith] with x' hx'
  use s, this
  have A : Icc x' (x' + s) subseteq Icc x (x + r') := by
    apply Icc_subset_Icc hx'.1.le
    linarith [hx'.2]
  intro y hy z hz
  exact hr' y (A hy) z (A hz)

/--
theorem `B_mem_nhdsGT` / 定理 `B_mem_nhdsGT`

English:
theorem B_mem_nhdsGT
  given: {K : Set F} {r s ε x : Real} (hx : x in B f K r s ε)
  proof: by
  obtain ⟨L, LK, hL₁, hL₂⟩ : exists L : F, L in K ∧ x in A f L r ε ∧ x in A f L s ε := by
    simpa only [B, mem_iUnion, mem_inter_iff, exists_prop] using hx
  filter_upwards [A_mem_nhdsGT hL₁, A_mem_nhdsGT hL₂] with y hy₁ hy₂
  simp only [B, mem_iUnion, mem_inter_iff, exists_prop]
  exact ⟨L, LK

中文:
定理 B_mem_nhdsGT
  条件: {K : Set F} {r s ε x : 实数} (hx : x in B f K r s ε)
  证明: by
  obtain ⟨L, LK, hL₁, hL₂⟩ : exists L : F, L in K ∧ x in A f L r ε ∧ x in A f L s ε := by
    simpa only [B, mem_iUnion, mem_inter_iff, exists_prop] using hx
  filter_upwards [A_mem_nhdsGT hL₁, A_mem_nhdsGT hL₂] with y hy₁ hy₂
  simp only [B, mem_iUnion, mem_inter_iff, exists_prop]
  exact ⟨L, LK

Depends on / 依赖: A_mem_nhdsGT, exists_prop, filter_upwards, mem_iUnion, mem_inter_iff
-/
theorem B_mem_nhdsGT {K : Set F} {r s ε x : Real} (hx : x in B f K r s ε) :
    B f K r s ε in 𝓝[>] x := by
  obtain ⟨L, LK, hL₁, hL₂⟩ : exists L : F, L in K ∧ x in A f L r ε ∧ x in A f L s ε := by
    simpa only [B, mem_iUnion, mem_inter_iff, exists_prop] using hx
  filter_upwards [A_mem_nhdsGT hL₁, A_mem_nhdsGT hL₂] with y hy₁ hy₂
  simp only [B, mem_iUnion, mem_inter_iff, exists_prop]
  exact ⟨L, LK, hy₁, hy₂⟩

/--
theorem `measurableSet_B` / 定理 `measurableSet_B`

English:
theorem measurableSet_B
  given: {K : Set F} {r s ε : Real}
  statement: MeasurableSet (B f K r s ε)
  proof: .of_mem_nhdsGT fun _ hx => B_mem_nhdsGT hx

中文:
定理 measurableSet_B
  条件: {K : Set F} {r s ε : 实数}
  结论: MeasurableSet (B f K r s ε)
  证明: .of_mem_nhdsGT fun _ hx => B_mem_nhdsGT hx

Depends on / 依赖: B_mem_nhdsGT, of_mem_nhdsGT
-/
theorem measurableSet_B {K : Set F} {r s ε : Real} : MeasurableSet (B f K r s ε) :=
  .of_mem_nhdsGT fun _ hx => B_mem_nhdsGT hx

/--
theorem `A_mono` / 定理 `A_mono`

English:
theorem A_mono
  given: (L : F) (r : Real) {ε δ : Real} (h : ε <= δ)
  statement: A f L r ε subseteq A f L r δ
  proof: by
  rintro x ⟨r', r'r, hr'⟩
  refine ⟨r', r'r, fun y hy z hz => (hr' y hy z hz).trans (mul_le_mul_of_nonneg_right h ?_)⟩
  linarith [hy.1, hy.2, r'r.2]

中文:
定理 A_mono
  条件: (L : F) (r : 实数) {ε δ : 实数} (h : ε <= δ)
  结论: A f L r ε subseteq A f L r δ
  证明: by
  rintro x ⟨r', r'r, hr'⟩
  refine ⟨r', r'r, fun y hy z hz => (hr' y hy z hz).trans (mul_le_mul_of_nonneg_right h ?_)⟩
  linarith [hy.1, hy.2, r'r.2]

Depends on / 依赖: mul_le_mul_of_nonneg_right
-/
theorem A_mono (L : F) (r : Real) {ε δ : Real} (h : ε <= δ) : A f L r ε subseteq A f L r δ := by
  rintro x ⟨r', r'r, hr'⟩
  refine ⟨r', r'r, fun y hy z hz => (hr' y hy z hz).trans (mul_le_mul_of_nonneg_right h ?_)⟩
  linarith [hy.1, hy.2, r'r.2]

/--
theorem `le_of_mem_A` / 定理 `le_of_mem_A`

English:
theorem le_of_mem_A
  statement: {r ε : Real} {L : F} {x : Real} (hx : x in A f L r ε) {y z : Real}
  proof: by
  rcases hx with ⟨r', r'mem, hr'⟩
  have A : x + r / 2 <= x + r' := by linarith [r'mem.1]
  exact hr' _ ((Icc_subset_Icc le_rfl A) hy) _ ((Icc_subset_Icc le_rfl A) hz)

中文:
定理 le_of_mem_A
  结论: {r ε : 实数} {L : F} {x : 实数} (hx : x in A f L r ε) {y z : 实数}
  证明: by
  rcases hx with ⟨r', r'mem, hr'⟩
  have A : x + r / 2 <= x + r' := by linarith [r'mem.1]
  exact hr' _ ((Icc_subset_Icc le_rfl A) hy) _ ((Icc_subset_Icc le_rfl A) hz)

Depends on / 依赖: Icc_subset_Icc, le_rfl
-/
theorem le_of_mem_A {r ε : Real} {L : F} {x : Real} (hx : x in A f L r ε) {y z : Real}
    (hy : y in Icc x (x + r / 2)) (hz : z in Icc x (x + r / 2)) :
    ‖f z - f y - (z - y) • L‖ <= ε * r := by
  rcases hx with ⟨r', r'mem, hr'⟩
  have A : x + r / 2 <= x + r' := by linarith [r'mem.1]
  exact hr' _ ((Icc_subset_Icc le_rfl A) hy) _ ((Icc_subset_Icc le_rfl A) hz)

/--
theorem `mem_A_of_differentiable` / 定理 `mem_A_of_differentiable`

English:
theorem mem_A_of_differentiable
  statement: {ε : Real} (hε : 0 < ε) {x : Real}
  proof: by
  have := hx.hasDerivWithinAt
  simp_rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff] at this
  rcases mem_nhdsGE_iff_exists_Ico_subset.1 (this (half_pos hε)) with ⟨m, xm, hm⟩
  refine ⟨m - x, by linarith [show x < m from xm], fun r hr => ?_⟩
  have : r in Ioc (r / 2) r := ⟨half_lt_self hr.1, l

中文:
定理 mem_A_of_differentiable
  结论: {ε : 实数} (hε : 0 < ε) {x : 实数}
  证明: by
  have := hx.hasDerivWithinAt
  simp_rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff] at this
  rcases mem_nhdsGE_iff_exists_Ico_subset.1 (this (half_pos hε)) with ⟨m, xm, hm⟩
  refine ⟨m - x, by linarith [show x < m from xm], fun r hr => ?_⟩
  have : r in Ioc (r / 2) r := ⟨half_lt_self hr.1, l

Depends on / 依赖: derivWithin, half_lt_self, half_pos, hasDerivWithinAt, hasDerivWithinAt_iff_isLittleO, hx.hasDerivWithinAt, isLittleO_iff, le_rfl, mem_nhdsGE_iff_exists_Ico_subset, simp_rw
-/
theorem mem_A_of_differentiable {ε : Real} (hε : 0 < ε) {x : Real}
    (hx : DifferentiableWithinAt Real f (Ici x) x) :
    exists R > 0, forall r in Ioo (0 : Real) R, x in A f (derivWithin f (Ici x) x) r ε := by
  have := hx.hasDerivWithinAt
  simp_rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff] at this
  rcases mem_nhdsGE_iff_exists_Ico_subset.1 (this (half_pos hε)) with ⟨m, xm, hm⟩
  refine ⟨m - x, by linarith [show x < m from xm], fun r hr => ?_⟩
  have : r in Ioc (r / 2) r := ⟨half_lt_self hr.1, le_rfl⟩
  refine ⟨r, this, fun y hy z hz => ?_⟩
  calc
    ‖f z - f y - (z - y) • derivWithin f (Ici x) x‖ =
        ‖f z - f x - (z - x) • derivWithin f (Ici x) x -
            (f y - f x - (y - x) • derivWithin f (Ici x) x)‖ := by
      congr 1; simp only [sub_smul]; abel
    _ <=
        ‖f z - f x - (z - x) • derivWithin f (Ici x) x‖ +
          ‖f y - f x - (y - x) • derivWithin f (Ici x) x‖ :=
      (norm_sub_le _ _)
    _ <= ε / 2 * ‖z - x‖ + ε / 2 * ‖y - x‖ :=
      (add_le_add (hm ⟨hz.1, hz.2.trans_lt (by linarith [hr.2])⟩)
        (hm ⟨hy.1, hy.2.trans_lt (by linarith [hr.2])⟩))
    _ <= ε / 2 * r + ε / 2 * r := by
      gcongr
      · rw [Real.norm_of_nonneg] <;> linarith [hz.1, hz.2]
      · rw [Real.norm_of_nonneg] <;> linarith [hy.1, hy.2]
    _ = ε * r := by ring

/--
theorem `norm_sub_le_of_mem_A` / 定理 `norm_sub_le_of_mem_A`

English:
theorem norm_sub_le_of_mem_A
  statement: {r x : Real} (hr : 0 < r) (ε : Real) {L₁ L₂ : F} (h₁ : x in A f L₁ r ε)
  proof: by
  suffices H : ‖(r / 2) • (L₁ - L₂)‖ <= r / 2 * (4 * ε) by
    rwa [norm_smul, Real.norm_of_nonneg (half_pos hr).le, mul_le_mul_iff_right₀ (half_pos hr)] at H
  calc
    ‖(r / 2) • (L₁ - L₂)‖ =
        ‖f (x + r / 2) - f x - (x + r / 2 - x) • L₂ -
            (f (x + r / 2) - f x - (x + r / 2 - x

中文:
定理 norm_sub_le_of_mem_A
  结论: {r x : 实数} (hr : 0 < r) (ε : 实数) {L₁ L₂ : F} (h₁ : x in A f L₁ r ε)
  证明: by
  suffices H : ‖(r / 2) • (L₁ - L₂)‖ <= r / 2 * (4 * ε) by
    rwa [norm_smul, Real.norm_of_nonneg (half_pos hr).le, mul_le_mul_iff_right₀ (half_pos hr)] at H
  calc
    ‖(r / 2) • (L₁ - L₂)‖ =
        ‖f (x + r / 2) - f x - (x + r / 2 - x) • L₂ -
            (f (x + r / 2) - f x - (x + r / 2 - x

Depends on / 依赖: Real.norm_of_nonneg, add_le_add, half_pos, le_of_mem_A, norm_of_nonneg, norm_smul, norm_sub_le, smul_sub
-/
theorem norm_sub_le_of_mem_A {r x : Real} (hr : 0 < r) (ε : Real) {L₁ L₂ : F} (h₁ : x in A f L₁ r ε)
    (h₂ : x in A f L₂ r ε) : ‖L₁ - L₂‖ <= 4 * ε := by
  suffices H : ‖(r / 2) • (L₁ - L₂)‖ <= r / 2 * (4 * ε) by
    rwa [norm_smul, Real.norm_of_nonneg (half_pos hr).le, mul_le_mul_iff_right₀ (half_pos hr)] at H
  calc
    ‖(r / 2) • (L₁ - L₂)‖ =
        ‖f (x + r / 2) - f x - (x + r / 2 - x) • L₂ -
            (f (x + r / 2) - f x - (x + r / 2 - x) • L₁)‖ := by
      simp [smul_sub]
    _ <= ‖f (x + r / 2) - f x - (x + r / 2 - x) • L₂‖ +
          ‖f (x + r / 2) - f x - (x + r / 2 - x) • L₁‖ :=
      norm_sub_le _ _
    _ <= ε * r + ε * r := by
      apply add_le_add
      · apply le_of_mem_A h₂ <;> simp [(half_pos hr).le]
      · apply le_of_mem_A h₁ <;> simp [(half_pos hr).le]
    _ = r / 2 * (4 * ε) := by ring

/--
theorem `differentiable_set_subset_D` / 定理 `differentiable_set_subset_D`

English:
theorem differentiable_set_subset_D
  proof: by
  intro x hx
  rw [D]; rw [mem_iInter]
  intro e
  have : (0 : Real) < (1 / 2) ^ e := pow_pos (by norm_num) _
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩
  obtain ⟨n, hn⟩ : exists n : Nat, (1 / 2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : Real) / 2 < 1)
 

中文:
定理 differentiable_set_subset_D
  证明: by
  intro x hx
  rw [D]; rw [mem_iInter]
  intro e
  have : (0 : Real) < (1 / 2) ^ e := pow_pos (by norm_num) _
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩
  obtain ⟨n, hn⟩ : exists n : Nat, (1 / 2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : Real) / 2 < 1)
 

Depends on / 依赖: R_pos, derivWithin, exists_pow_lt_of_lt_one, lt_of_le_of_lt, mem_A_of_differentiable, mem_iInter, mem_iUnion, mem_inter_iff, pow_le_pow_of_le_one, pow_pos
-/
theorem differentiable_set_subset_D :
    { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWithin f (Ici x) x in K } subseteq D f K := by
  intro x hx
  rw [D]; rw [mem_iInter]
  intro e
  have : (0 : Real) < (1 / 2) ^ e := pow_pos (by norm_num) _
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩
  obtain ⟨n, hn⟩ : exists n : Nat, (1 / 2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : Real) / 2 < 1)
  simp only [mem_iUnion, mem_iInter, B, mem_inter_iff]
  refine ⟨n, fun p hp q hq => ⟨derivWithin f (Ici x) x, hx.2, ⟨?_, ?_⟩⟩⟩ <;>
    · refine hR _ ⟨pow_pos (by norm_num) _, lt_of_le_of_lt ?_ hn⟩
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by assumption)

/--
theorem `D_subset_differentiable_set` / 定理 `D_subset_differentiable_set`

English:
theorem D_subset_differentiable_set
  given: {K : Set F} (hK : IsComplete K)
  proof: by
  have P : forall {n : Nat}, (0 : Real) < (1 / 2) ^ n := fun {n} => pow_pos (by norm_num) n
  intro x hx
  have :
    forall e : Nat, exists n : Nat, forall p q, n <= p -> n <= q ->
      exists L in K, x in A f L ((1 / 2) ^ p) ((1 / 2) ^ e) inter A f L ((1 / 2) ^ q) ((1 / 2) ^ e) := by
    intro

中文:
定理 D_subset_differentiable_set
  条件: {K : Set F} (hK : IsComplete K)
  证明: by
  have P : forall {n : Nat}, (0 : Real) < (1 / 2) ^ n := fun {n} => pow_pos (by norm_num) n
  intro x hx
  have :
    forall e : Nat, exists n : Nat, forall p q, n <= p -> n <= q ->
      exists L in K, x in A f L ((1 / 2) ^ p) ((1 / 2) ^ e) inter A f L ((1 / 2) ^ q) ((1 / 2) ^ e) := by
    intro

Depends on / 依赖: exists_prop, exists_prop.mp, mem_iInter, mem_iUnion, pow_pos
-/
theorem D_subset_differentiable_set {K : Set F} (hK : IsComplete K) :
    D f K subseteq { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWithin f (Ici x) x in K } := by
  have P : forall {n : Nat}, (0 : Real) < (1 / 2) ^ n := fun {n} => pow_pos (by norm_num) n
  intro x hx
  have :
    forall e : Nat, exists n : Nat, forall p q, n <= p -> n <= q ->
      exists L in K, x in A f L ((1 / 2) ^ p) ((1 / 2) ^ e) inter A f L ((1 / 2) ^ q) ((1 / 2) ^ e) := by
    intro e
    have := mem_iInter.1 hx e
    rcases mem_iUnion.1 this with ⟨n, hn⟩
    refine ⟨n, fun p q hp hq => ?_⟩
    simp only [mem_iInter] at hn
    rcases mem_iUnion.1 (hn p hp q hq) with ⟨L, hL⟩
exact ⟨L, exists_prop.mp mem_iUnion.1 hL⟩
  /- Recast the assumptions: for each `e`, there exist `n e` and linear maps `L e p q` in `K`
    such that, for `p, q ≥ n e`, then `f` is well approximated by `L e p q` at scale `2 ^ (-p)` and
    `2 ^ (-q)`, with an error `2 ^ (-e)`. -/
  choose! n L hn using this
  /- All the operators `L e p q` that show up are close to each other. To prove this, we argue
      that `L e p q` is close to `L e p r` (where `r` is large enough), as both approximate `f` at
      scale `2 ^(- p)`. And `L e p r` is close to `L e' p' r` as both approximate `f` at scale
      `2 ^ (- r)`. And `L e' p' r` is close to `L e' p' q'` as both approximate `f` at scale
      `2 ^ (- p')`. -/
  have M :
    forall e p q e' p' q',
      n e <= p ->
        n e <= q -> n e' <= p' -> n e' <= q' -> e <= e' -> ‖L e p q - L e' p' q'‖ <= 12 * (1 / 2) ^ e := by
    intro e p q e' p' q' hp hq hp' hq' he'
    let r := max (n e) (n e')
    have I : ((1 : Real) / 2) ^ e' <= (1 / 2) ^ e :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) he'
    have J1 : ‖L e p q - L e p r‖ <= 4 * (1 / 2) ^ e := by
      have I1 : x in A f (L e p q) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p q hp hq).2.1
      have I2 : x in A f (L e p r) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p r hp (le_max_left _ _)).2.1
      exact norm_sub_le_of_mem_A P _ I1 I2
    have J2 : ‖L e p r - L e' p' r‖ <= 4 * (1 / 2) ^ e := by
      have I1 : x in A f (L e p r) ((1 / 2) ^ r) ((1 / 2) ^ e) := (hn e p r hp (le_max_left _ _)).2.2
      have I2 : x in A f (L e' p' r) ((1 / 2) ^ r) ((1 / 2) ^ e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.2
      exact norm_sub_le_of_mem_A P _ I1 (A_mono _ _ I I2)
    have J3 : ‖L e' p' r - L e' p' q'‖ <= 4 * (1 / 2) ^ e := by
      have I1 : x in A f (L e' p' r) ((1 / 2) ^ p') ((1 / 2) ^ e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.1
      have I2 : x in A f (L e' p' q') ((1 / 2) ^ p') ((1 / 2) ^ e') := (hn e' p' q' hp' hq').2.1
      exact norm_sub_le_of_mem_A P _ (A_mono _ _ I I1) (A_mono _ _ I I2)
    calc
      ‖L e p q - L e' p' q'‖ =
          ‖L e p q - L e p r + (L e p r - L e' p' r) + (L e' p' r - L e' p' q')‖ := by
        congr 1; abel
      _ <= ‖L e p q - L e p r‖ + ‖L e p r - L e' p' r‖ + ‖L e' p' r - L e' p' q'‖ := by
        grw [norm_add_le, norm_add_le]
      _ <= 4 * (1 / 2) ^ e + 4 * (1 / 2) ^ e + 4 * (1 / 2) ^ e := by gcongr
      _ = 12 * (1 / 2) ^ e := by ring
  /- For definiteness, use `L0 e = L e (n e) (n e)`, to have a single sequence. We claim that this
    is a Cauchy sequence. -/
  let L0 : Nat -> F := fun e => L e (n e) (n e)
  have : CauchySeq L0 := by
    rw [Metric.cauchySeq_iff']
    intro ε εpos
    obtain ⟨e, he⟩ : exists e : Nat, (1 / 2) ^ e < ε / 12 :=
      exists_pow_lt_of_lt_one (div_pos εpos (by norm_num)) (by norm_num)
    refine ⟨e, fun e' he' => ?_⟩
    rw [dist_comm]; rw [dist_eq_norm]
    calc
      ‖L0 e - L0 e'‖ <= 12 * (1 / 2) ^ e := M _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl he'
      _ < 12 * (ε / 12) := mul_lt_mul' le_rfl he (le_of_lt P) (by norm_num)
      _ = ε := by ring
  -- As it is Cauchy, the sequence `L0` converges, to a limit `f'` in `K`.
  obtain ⟨f', f'K, hf'⟩ : exists f' in K, Tendsto L0 atTop (𝓝 f') :=
    cauchySeq_tendsto_of_isComplete hK (fun e => (hn e (n e) (n e) le_rfl le_rfl).1) this
  have Lf' : forall e p, n e <= p -> ‖L e (n e) p - f'‖ <= 12 * (1 / 2) ^ e := by
    intro e p hp
    apply le_of_tendsto (tendsto_const_nhds.sub hf').norm
    rw [eventually_atTop]
    exact ⟨e, fun e' he' => M _ _ _ _ _ _ le_rfl hp le_rfl le_rfl he'⟩
  -- Let us show that `f` has right derivative `f'` at `x`.
  have : HasDerivWithinAt f f' (Ici x) x := by
    simp only [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
    /- to get an approximation with a precision `ε`, we will replace `f` with `L e (n e) m` for
      some large enough `e` (yielding a small error by uniform approximation). As one can vary `m`,
      this makes it possible to cover all scales, and thus to obtain a good linear approximation in
      the whole interval of length `(1/2)^(n e)`. -/
    intro ε εpos
    obtain ⟨e, he⟩ : exists e : Nat, (1 / 2) ^ e < ε / 16 :=
      exists_pow_lt_of_lt_one (div_pos εpos (by norm_num)) (by norm_num)
    filter_upwards [Icc_mem_nhdsGE <| show x < x + (1 / 2) ^ (n e + 1) by simp] with y hy
    -- We need to show that `f y - f x - f' (y - x)` is small. For this, we will work at scale
    -- `k` where `k` is chosen with `‖y - x‖ ∼ 2 ^ (-k)`.
    rcases eq_or_lt_of_le hy.1 with (rfl | xy)
    · simp only [sub_self, zero_smul, norm_zero, mul_zero, le_rfl]
    have yzero : 0 < y - x := sub_pos.2 xy
    have y_le : y - x <= (1 / 2) ^ (n e + 1) := by linarith [hy.2]
    have yone : y - x <= 1 := le_trans y_le (pow_le_one₀ (by norm_num) (by norm_num))
    -- define the scale `k`.
    obtain ⟨k, hk, h'k⟩ : exists k : Nat, (1 / 2) ^ (k + 1) < y - x ∧ y - x <= (1 / 2) ^ k :=
      exists_nat_pow_near_of_lt_one yzero yone (by norm_num : (0 : Real) < 1 / 2)
        (by norm_num : (1 : Real) / 2 < 1)
    -- the scale is large enough (as `y - x` is small enough)
    have k_gt : n e < k := by
      have : ((1 : Real) / 2) ^ (k + 1) < (1 / 2) ^ (n e + 1) := lt_of_lt_of_le hk y_le
      rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : Real) < 1 / 2) (by norm_num)] at this
      lia
    set m := k - 1
    have m_ge : n e <= m := Nat.le_sub_one_of_lt k_gt
    have km : k = m + 1 := (Nat.succ_pred_eq_of_pos k_gt.pos).symm
    rw [km] at hk h'k
    -- `f` is well approximated by `L e (n e) k` at the relevant scale
    -- (in fact, we use `m = k - 1` instead of `k` because of the precise definition of `A`).
    have J : ‖f y - f x - (y - x) • L e (n e) m‖ <= 4 * (1 / 2) ^ e * ‖y - x‖ :=
      calc
        ‖f y - f x - (y - x) • L e (n e) m‖ <= (1 / 2) ^ e * (1 / 2) ^ m := by
          apply le_of_mem_A (hn e (n e) m le_rfl m_ge).2.2
          · simp only [one_div, inv_pow, left_mem_Icc, le_add_iff_nonneg_right]
            positivity
          · simp only [pow_add, tsub_le_iff_left] at h'k
            simpa only [hy.1, mem_Icc, true_and, one_div, pow_one] using! h'k
        _ = 4 * (1 / 2) ^ e * (1 / 2) ^ (m + 2) := by ring
        _ <= 4 * (1 / 2) ^ e * (y - x) := by gcongr
        _ = 4 * (1 / 2) ^ e * ‖y - x‖ := by rw [Real.norm_of_nonneg yzero.le]
    calc
      ‖f y - f x - (y - x) • f'‖ =
          ‖f y - f x - (y - x) • L e (n e) m + (y - x) • (L e (n e) m - f')‖ := by
        simp only [smul_sub, sub_add_sub_cancel]
      _ <= 4 * (1 / 2) ^ e * ‖y - x‖ + ‖y - x‖ * (12 * (1 / 2) ^ e) :=
norm_add_le_of_le J by rw [norm_smul]; gcongr; exact Lf' _ _ m_ge
      _ = 16 * ‖y - x‖ * (1 / 2) ^ e := by ring
      _ <= 16 * ‖y - x‖ * (ε / 16) := by gcongr
      _ = ε * ‖y - x‖ := by ring
  -- Conclusion of the proof
  rw [← this.derivWithin (uniqueDiffOn_Ici x x Set.self_mem_Ici)] at f'K
  exact ⟨this.differentiableWithinAt, f'K⟩

/--
theorem `differentiable_set_eq_D` / 定理 `differentiable_set_eq_D`

English:
theorem differentiable_set_eq_D
  given: (hK : IsComplete K)
  proof: Subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

中文:
定理 differentiable_set_eq_D
  条件: (hK : IsComplete K)
  证明: Subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

Depends on / 依赖: D_subset_differentiable_set, Subset, Subset.antisymm, antisymm, differentiable_set_subset_D
-/
theorem differentiable_set_eq_D (hK : IsComplete K) :
    { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWithin f (Ici x) x in K } = D f K :=
  Subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

end RightDerivMeasurableAux

open RightDerivMeasurableAux

variable (f)

/--
theorem `measurableSet_of_differentiableWithinAt_Ici_of_isComplete` / 定理 `measurableSet_of_differentiableWithinAt_Ici_of_isComplete`

English:
theorem measurableSet_of_differentiableWithinAt_Ici_of_isComplete
  given: {K : Set F} (hK : IsComplete K)
  proof: by
  -- simp [differentiable_set_eq_d K hK, D, measurableSet_b, MeasurableSet.iInter,
  -- MeasurableSet.iUnion]
  simp only [differentiable_set_eq_D K hK, D]
  repeat apply_rules [MeasurableSet.iUnion, MeasurableSet.iInter] <;> intro
  exact measurableSet_B

中文:
定理 measurableSet_of_differentiableWithinAt_Ici_of_isComplete
  条件: {K : Set F} (hK : IsComplete K)
  证明: by
  -- simp [differentiable_set_eq_d K hK, D, measurableSet_b, MeasurableSet.iInter,
  -- MeasurableSet.iUnion]
  simp only [differentiable_set_eq_D K hK, D]
  repeat apply_rules [MeasurableSet.iUnion, MeasurableSet.iInter] <;> intro
  exact measurableSet_B
-/
theorem measurableSet_of_differentiableWithinAt_Ici_of_isComplete {K : Set F} (hK : IsComplete K) :
    MeasurableSet { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWithin f (Ici x) x in K } := by
  -- simp [differentiable_set_eq_d K hK, D, measurableSet_b, MeasurableSet.iInter,
  -- MeasurableSet.iUnion]
  simp only [differentiable_set_eq_D K hK, D]
  repeat apply_rules [MeasurableSet.iUnion, MeasurableSet.iInter] <;> intro
  exact measurableSet_B

variable [CompleteSpace F]

/--
theorem `measurableSet_of_differentiableWithinAt_Ici` / 定理 `measurableSet_of_differentiableWithinAt_Ici`

English:
theorem measurableSet_of_differentiableWithinAt_Ici
  proof: by
  have : IsComplete (univ : Set F) := isComplete_univ
  convert! measurableSet_of_differentiableWithinAt_Ici_of_isComplete f this
  simp

@[fun_prop]

中文:
定理 measurableSet_of_differentiableWithinAt_Ici
  证明: by
  have : IsComplete (univ : Set F) := isComplete_univ
  convert! measurableSet_of_differentiableWithinAt_Ici_of_isComplete f this
  simp

@[fun_prop]

Depends on / 依赖: IsComplete, StrictConvexSpace, Submodule, Submodule.instStrictConvexSpace, convert, instStrictConvexSpace, isComplete_univ, measurableSet_of_differentiableWithinAt_Ici_of_isComplete
-/
theorem measurableSet_of_differentiableWithinAt_Ici :
    MeasurableSet { x | DifferentiableWithinAt Real f (Ici x) x } := by
  have : IsComplete (univ : Set F) := isComplete_univ
  convert! measurableSet_of_differentiableWithinAt_Ici_of_isComplete f this
  simp

@[fun_prop]
/--
theorem `measurable_derivWithin_Ici` / 定理 `measurable_derivWithin_Ici`

English:
theorem measurable_derivWithin_Ici
  given: [MeasurableSpace F] [BorelSpace F]
  proof: by
  refine measurable_of_isClosed fun s hs => ?_
  have :
    (fun x => derivWithin f (Ici x) x) ⁻¹' s =
      { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWithin f (Ici x) x in s } union
        { x | ¬DifferentiableWithinAt Real f (Ici x) x } inter { _x | (0 : F) in s } :=
    Set.ext fun

中文:
定理 measurable_derivWithin_Ici
  条件: [MeasurableSpace F] [BorelSpace F]
  证明: by
  refine measurable_of_isClosed fun s hs => ?_
  have :
    (fun x => derivWithin f (Ici x) x) ⁻¹' s =
      { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWithin f (Ici x) x in s } union
        { x | ¬DifferentiableWithinAt Real f (Ici x) x } inter { _x | (0 : F) in s } :=
    Set.ext fun

Depends on / 依赖: DifferentiableWithinAt, MeasurableSet, MeasurableSet.const, Set.ext, compl.inter, derivWithin, derivWithin_mem_iff, hs.isComplete, isComplete, measurableSet_of_differentiableWithinAt_Ici, measurableSet_of_differentiableWithinAt_Ici_of_isComplete, measurable_of_isClosed, mem_preimage, mem_preimage.trans
-/
theorem measurable_derivWithin_Ici [MeasurableSpace F] [BorelSpace F] :
    Measurable fun x => derivWithin f (Ici x) x := by
  refine measurable_of_isClosed fun s hs => ?_
  have :
    (fun x => derivWithin f (Ici x) x) ⁻¹' s =
      { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWithin f (Ici x) x in s } union
        { x | ¬DifferentiableWithinAt Real f (Ici x) x } inter { _x | (0 : F) in s } :=
    Set.ext fun x => mem_preimage.trans derivWithin_mem_iff
  rw [this]
  exact
    (measurableSet_of_differentiableWithinAt_Ici_of_isComplete _ hs.isComplete).union
      ((measurableSet_of_differentiableWithinAt_Ici _).compl.inter (MeasurableSet.const _))

/--
theorem `stronglyMeasurable_derivWithin_Ici` / 定理 `stronglyMeasurable_derivWithin_Ici`

English:
theorem stronglyMeasurable_derivWithin_Ici
  proof: by
  borelize F
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_derivWithin_Ici f, ?_⟩
  obtain ⟨t, t_count, ht⟩ : exists t : Set Real, t.Countable ∧ Dense t := exists_countable_dense Real
  suffices H : range (fun x => derivWithin f (Ici x) x) subseteq closure (Submodule.span Real

中文:
定理 stronglyMeasurable_derivWithin_Ici
  证明: by
  borelize F
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_derivWithin_Ici f, ?_⟩
  obtain ⟨t, t_count, ht⟩ : exists t : Set Real, t.Countable ∧ Dense t := exists_countable_dense Real
  suffices H : range (fun x => derivWithin f (Ici x) x) subseteq closure (Submodule.span Real

Depends on / 依赖: Countable, IsSeparable, IsSeparable.mono, Submodule, Submodule.span, borelize, closure, derivWithin, exists_countable_dense, isSeparable, isSeparable.span.closure, measurable_derivWithin_Ici, stronglyMeasurable_iff_measurable_separable, subseteq, t.Countable, t_count, t_count.image
-/
theorem stronglyMeasurable_derivWithin_Ici :
    StronglyMeasurable (fun x => derivWithin f (Ici x) x) := by
  borelize F
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_derivWithin_Ici f, ?_⟩
  obtain ⟨t, t_count, ht⟩ : exists t : Set Real, t.Countable ∧ Dense t := exists_countable_dense Real
  suffices H : range (fun x => derivWithin f (Ici x) x) subseteq closure (Submodule.span Real (f '' t)) from
    IsSeparable.mono (t_count.image f).isSeparable.span.closure H
  rintro - ⟨x, rfl⟩
  suffices H' : range (fun y => derivWithin f (Ici x) y) subseteq closure (Submodule.span Real (f '' t)) from
    H' (mem_range_self _)
  apply range_derivWithin_subset_closure_span_image
  calc Ici x
    = closure (Ioi x inter closure t) := by simp [dense_iff_closure_eq.1 ht]
  _ subseteq closure (closure (Ioi x inter t)) := by
      apply closure_mono
      simpa [inter_comm] using (isOpen_Ioi (a := x)).closure_inter (s := t)
  _ subseteq closure (Ici x inter t) := by
      rw [closure_closure]
      exact closure_mono (inter_subset_inter_left _ Ioi_subset_Ici_self)

/--
theorem `aemeasurable_derivWithin_Ici` / 定理 `aemeasurable_derivWithin_Ici`

English:
theorem aemeasurable_derivWithin_Ici
  given: [MeasurableSpace F] [BorelSpace F] (μ : Measure Real)
  proof: (measurable_derivWithin_Ici f).aemeasurable

中文:
定理 aemeasurable_derivWithin_Ici
  条件: [MeasurableSpace F] [BorelSpace F] (μ : Measure 实数)
  证明: (measurable_derivWithin_Ici f).aemeasurable

Depends on / 依赖: aemeasurable, measurable_derivWithin_Ici
-/
theorem aemeasurable_derivWithin_Ici [MeasurableSpace F] [BorelSpace F] (μ : Measure Real) :
    AEMeasurable (fun x => derivWithin f (Ici x) x) μ :=
  (measurable_derivWithin_Ici f).aemeasurable

/--
theorem `aestronglyMeasurable_derivWithin_Ici` / 定理 `aestronglyMeasurable_derivWithin_Ici`

English:
theorem aestronglyMeasurable_derivWithin_Ici
  given: (μ : Measure Real)
  proof: (stronglyMeasurable_derivWithin_Ici f).aestronglyMeasurable

中文:
定理 aestronglyMeasurable_derivWithin_Ici
  条件: (μ : Measure 实数)
  证明: (stronglyMeasurable_derivWithin_Ici f).aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, stronglyMeasurable_derivWithin_Ici
-/
theorem aestronglyMeasurable_derivWithin_Ici (μ : Measure Real) :
    AEStronglyMeasurable (fun x => derivWithin f (Ici x) x) μ :=
  (stronglyMeasurable_derivWithin_Ici f).aestronglyMeasurable

/--
theorem `measurableSet_of_differentiableWithinAt_Ioi` / 定理 `measurableSet_of_differentiableWithinAt_Ioi`

English:
theorem measurableSet_of_differentiableWithinAt_Ioi
  proof: by
  simpa [differentiableWithinAt_Ioi_iff_Ici] using measurableSet_of_differentiableWithinAt_Ici f

@[fun_prop]

中文:
定理 measurableSet_of_differentiableWithinAt_Ioi
  证明: by
  simpa [differentiableWithinAt_Ioi_iff_Ici] using measurableSet_of_differentiableWithinAt_Ici f

@[fun_prop]

Depends on / 依赖: differentiableWithinAt_Ioi_iff_Ici, measurableSet_of_differentiableWithinAt_Ici
-/
theorem measurableSet_of_differentiableWithinAt_Ioi :
    MeasurableSet { x | DifferentiableWithinAt Real f (Ioi x) x } := by
  simpa [differentiableWithinAt_Ioi_iff_Ici] using measurableSet_of_differentiableWithinAt_Ici f

@[fun_prop]
/--
theorem `measurable_derivWithin_Ioi` / 定理 `measurable_derivWithin_Ioi`

English:
theorem measurable_derivWithin_Ioi
  given: [MeasurableSpace F] [BorelSpace F]
  proof: by
  simpa [derivWithin_Ioi_eq_Ici] using measurable_derivWithin_Ici f

中文:
定理 measurable_derivWithin_Ioi
  条件: [MeasurableSpace F] [BorelSpace F]
  证明: by
  simpa [derivWithin_Ioi_eq_Ici] using measurable_derivWithin_Ici f

Depends on / 依赖: derivWithin_Ioi_eq_Ici, measurable_derivWithin_Ici
-/
theorem measurable_derivWithin_Ioi [MeasurableSpace F] [BorelSpace F] :
    Measurable fun x => derivWithin f (Ioi x) x := by
  simpa [derivWithin_Ioi_eq_Ici] using measurable_derivWithin_Ici f

/--
theorem `stronglyMeasurable_derivWithin_Ioi` / 定理 `stronglyMeasurable_derivWithin_Ioi`

English:
theorem stronglyMeasurable_derivWithin_Ioi
  proof: by
  simpa [derivWithin_Ioi_eq_Ici] using stronglyMeasurable_derivWithin_Ici f

中文:
定理 stronglyMeasurable_derivWithin_Ioi
  证明: by
  simpa [derivWithin_Ioi_eq_Ici] using stronglyMeasurable_derivWithin_Ici f

Depends on / 依赖: derivWithin_Ioi_eq_Ici, stronglyMeasurable_derivWithin_Ici
-/
theorem stronglyMeasurable_derivWithin_Ioi :
    StronglyMeasurable (fun x => derivWithin f (Ioi x) x) := by
  simpa [derivWithin_Ioi_eq_Ici] using stronglyMeasurable_derivWithin_Ici f

/--
theorem `aemeasurable_derivWithin_Ioi` / 定理 `aemeasurable_derivWithin_Ioi`

English:
theorem aemeasurable_derivWithin_Ioi
  given: [MeasurableSpace F] [BorelSpace F] (μ : Measure Real)
  proof: (measurable_derivWithin_Ioi f).aemeasurable

中文:
定理 aemeasurable_derivWithin_Ioi
  条件: [MeasurableSpace F] [BorelSpace F] (μ : Measure 实数)
  证明: (measurable_derivWithin_Ioi f).aemeasurable

Depends on / 依赖: aemeasurable, measurable_derivWithin_Ioi
-/
theorem aemeasurable_derivWithin_Ioi [MeasurableSpace F] [BorelSpace F] (μ : Measure Real) :
    AEMeasurable (fun x => derivWithin f (Ioi x) x) μ :=
  (measurable_derivWithin_Ioi f).aemeasurable

/--
theorem `aestronglyMeasurable_derivWithin_Ioi` / 定理 `aestronglyMeasurable_derivWithin_Ioi`

English:
theorem aestronglyMeasurable_derivWithin_Ioi
  given: (μ : Measure Real)
  proof: (stronglyMeasurable_derivWithin_Ioi f).aestronglyMeasurable

中文:
定理 aestronglyMeasurable_derivWithin_Ioi
  条件: (μ : Measure 实数)
  证明: (stronglyMeasurable_derivWithin_Ioi f).aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, stronglyMeasurable_derivWithin_Ioi
-/
theorem aestronglyMeasurable_derivWithin_Ioi (μ : Measure Real) :
    AEStronglyMeasurable (fun x => derivWithin f (Ioi x) x) μ :=
  (stronglyMeasurable_derivWithin_Ioi f).aestronglyMeasurable

end RightDeriv

section WithParam

/- In this section, we prove the measurability of the derivative in a context with parameters:
given `f : α → E → F`, we want to show that `p ↦ fderiv 𝕜 (f p.1) p.2` is measurable. Contrary
to the previous sections, some assumptions are needed for this: if `f p.1` depends arbitrarily on
`p.1`, this is obviously false. We require that `f` is continuous and `E` is locally compact --
then the proofs in the previous sections adapt readily, as the set `A` defined above is open, so
that the differentiability set `D` is measurable. -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {α : Type*} [TopologicalSpace α]
  {f : α -> E -> F}

namespace FDerivMeasurableAux

open Uniformity

/--
lemma `isOpen_A_with_param` / 引理 `isOpen_A_with_param`

English:
lemma isOpen_A_with_param
  given: {r s : Real} (hf : Continuous f.uncurry) (L : E ->L[𝕜] F)
  proof: by
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  simp only [A, mem_Ioc, mem_ball, map_sub, mem_ofPred_eq]
  apply isOpen_iff_mem_nhds.2
  rintro ⟨a, x⟩ ⟨r', ⟨Irr', Ir'r⟩, hr⟩
  rcases exists_between Irr' with ⟨t, hrt, htr'⟩
  rcases exists_between hrt with ⟨t', hrt', ht't⟩
  obtain ⟨b, b_lt,

中文:
引理 isOpen_A_with_param
  条件: {r s : 实数} (hf : Continuous f.uncurry) (L : E ->L[𝕜] F)
  证明: by
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  simp only [A, mem_Ioc, mem_ball, map_sub, mem_ofPred_eq]
  apply isOpen_iff_mem_nhds.2
  rintro ⟨a, x⟩ ⟨r', ⟨Irr', Ir'r⟩, hr⟩
  rcases exists_between Irr' with ⟨t, hrt, htr'⟩
  rcases exists_between hrt with ⟨t', hrt', ht't⟩
  obtain ⟨b, b_lt,

Depends on / 依赖: Continuous, ProperSpace, b_lt, closedBall, exists_between, isOpen_iff_mem_nhds, map_sub, mem_Ioc, mem_ball, mem_ofPred_eq, of_locallyCompactSpace
-/
lemma isOpen_A_with_param {r s : Real} (hf : Continuous f.uncurry) (L : E ->L[𝕜] F) :
    IsOpen {p : α × E | p.2 in A (f p.1) L r s} := by
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  simp only [A, mem_Ioc, mem_ball, map_sub, mem_ofPred_eq]
  apply isOpen_iff_mem_nhds.2
  rintro ⟨a, x⟩ ⟨r', ⟨Irr', Ir'r⟩, hr⟩
  rcases exists_between Irr' with ⟨t, hrt, htr'⟩
  rcases exists_between hrt with ⟨t', hrt', ht't⟩
  obtain ⟨b, b_lt, hb⟩ : exists b, b < s * r ∧ forall y in closedBall x t, forall z in closedBall x t,
      ‖f a z - f a y - (L z - L y)‖ <= b := by
    have B : Continuous (fun (p : E × E) => ‖f a p.2 - f a p.1 - (L p.2 - L p.1)‖) := by fun_prop
    have C : (closedBall x t ×ˢ closedBall x t).Nonempty := by simp; linarith
    rcases ((isCompact_closedBall x t).prod (isCompact_closedBall x t)).exists_isMaxOn
      C B.continuousOn with ⟨p, pt, hp⟩
    simp only [mem_prod, mem_closedBall] at pt
    refine ⟨‖f a p.2 - f a p.1 - (L p.2 - L p.1)‖,
      hr p.1 (pt.1.trans_lt htr') p.2 (pt.2.trans_lt htr'), fun y hy z hz => ?_⟩
    have D : (y, z) in closedBall x t ×ˢ closedBall x t := mem_prod.2 ⟨hy, hz⟩
    exact hp D
  obtain ⟨ε, εpos, hε⟩ : exists ε, 0 < ε ∧ b + 2 * ε < s * r :=
    ⟨(s * r - b) / 3, by linarith, by linarith⟩
  obtain ⟨u, u_open, au, hu⟩ : exists u, IsOpen u ∧ a in u ∧ forall (p : α × E),
      p.1 in u -> p.2 in closedBall x t -> dist (f.uncurry p) (f.uncurry (a, p.2)) < ε := by
    have C : Continuous (fun (p : α × E) => f a p.2) := by fun_prop
    have D : ({a} ×ˢ closedBall x t).EqOn f.uncurry (fun p => f a p.2) := by
      rintro ⟨b, y⟩ ⟨hb, -⟩
      simp only [mem_singleton_iff] at hb
      simp [hb]
    obtain ⟨v, v_open, sub_v, hv⟩ : exists v, IsOpen v ∧ {a} ×ˢ closedBall x t subseteq v ∧
        forall p in v, dist (Function.uncurry f p) (f a p.2) < ε :=
      Uniform.exists_is_open_mem_uniformity_of_forall_mem_eq (s := {a} ×ˢ closedBall x t)
        (fun p _ => hf.continuousAt) (fun p _ => C.continuousAt) D (dist_mem_uniformity εpos)
    obtain ⟨w, w', w_open, -, sub_w, sub_w', hww'⟩ : exists (w : Set α) (w' : Set E),
        IsOpen w ∧ IsOpen w' ∧ {a} subseteq w ∧ closedBall x t subseteq w' ∧ w ×ˢ w' subseteq v :=
      generalized_tube_lemma isCompact_singleton (isCompact_closedBall x t) v_open sub_v
    refine ⟨w, w_open, sub_w rfl, ?_⟩
    rintro ⟨b, y⟩ h hby
    exact hv _ (hww' ⟨h, sub_w' hby⟩)
  have : u ×ˢ ball x (t - t') in 𝓝 (a, x) :=
    prod_mem_nhds (u_open.mem_nhds au) (ball_mem_nhds _ (sub_pos.2 ht't))
  filter_upwards [this]
  rintro ⟨a', x'⟩ ha'x'
  simp only [mem_prod, mem_ball] at ha'x'
  refine ⟨t', ⟨hrt', ht't.le.trans (htr'.le.trans Ir'r)⟩, fun y hy z hz => ?_⟩
  have dyx : dist y x <= t := by linarith [dist_triangle y x' x]
  have dzx : dist z x <= t := by linarith [dist_triangle z x' x]
  calc
  ‖f a' z - f a' y - (L z - L y)‖ =
    ‖(f a' z - f a z) + (f a y - f a' y) + (f a z - f a y - (L z - L y))‖ := by congr; abel
  _ <= ‖f a' z - f a z‖ + ‖f a y - f a' y‖ + ‖f a z - f a y - (L z - L y)‖ := norm_add₃_le
  _ <= ε + ε + b := by
      gcongr
      · rw [← dist_eq_norm]
        change dist (f.uncurry (a', z)) (f.uncurry (a, z)) <= ε
        apply (hu _ _ _).le
        · exact ha'x'.1
        · simp [dzx]
      · rw [← dist_eq_norm']
        change dist (f.uncurry (a', y)) (f.uncurry (a, y)) <= ε
        apply (hu _ _ _).le
        · exact ha'x'.1
        · simp [dyx]
      · simp [hb, dyx, dzx]
  _ < s * r := by linarith

/--
lemma `isOpen_B_with_param` / 引理 `isOpen_B_with_param`

English:
lemma isOpen_B_with_param
  given: {r s t : Real} (hf : Continuous f.uncurry) (K : Set (E ->L[𝕜] F))
  proof: by
  suffices H : IsOpen (⋃ L in K,
      {p : α × E | p.2 in A (f p.1) L r t ∧ p.2 in A (f p.1) L s t}) by
    convert! H; ext p; simp [B]
  refine isOpen_biUnion (fun L _ => ?_)
  exact (isOpen_A_with_param hf L).inter (isOpen_A_with_param hf L)

中文:
引理 isOpen_B_with_param
  条件: {r s t : 实数} (hf : Continuous f.uncurry) (K : Set (E ->L[𝕜] F))
  证明: by
  suffices H : IsOpen (⋃ L in K,
      {p : α × E | p.2 in A (f p.1) L r t ∧ p.2 in A (f p.1) L s t}) by
    convert! H; ext p; simp [B]
  refine isOpen_biUnion (fun L _ => ?_)
  exact (isOpen_A_with_param hf L).inter (isOpen_A_with_param hf L)

Depends on / 依赖: IsOpen, convert, isOpen_A_with_param, isOpen_biUnion
-/
lemma isOpen_B_with_param {r s t : Real} (hf : Continuous f.uncurry) (K : Set (E ->L[𝕜] F)) :
    IsOpen {p : α × E | p.2 in B (f p.1) K r s t} := by
  suffices H : IsOpen (⋃ L in K,
      {p : α × E | p.2 in A (f p.1) L r t ∧ p.2 in A (f p.1) L s t}) by
    convert! H; ext p; simp [B]
  refine isOpen_biUnion (fun L _ => ?_)
  exact (isOpen_A_with_param hf L).inter (isOpen_A_with_param hf L)

end FDerivMeasurableAux

open FDerivMeasurableAux

variable [MeasurableSpace α] [OpensMeasurableSpace α] [MeasurableSpace E] [OpensMeasurableSpace E]

/--
theorem `measurableSet_of_differentiableAt_of_isComplete_with_param` / 定理 `measurableSet_of_differentiableAt_of_isComplete_with_param`

English:
theorem measurableSet_of_differentiableAt_of_isComplete_with_param
  proof: by
  have : {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 in K}
          = {p : α × E | p.2 in D (f p.1) K} := by simp [← differentiable_set_eq_D K hK]
  rw [this]
  simp only [D, mem_iInter, mem_iUnion]
  simp only [ofPred_forall, ofPred_exists]
  refine MeasurableSet.iInter (

中文:
定理 measurableSet_of_differentiableAt_of_isComplete_with_param
  证明: by
  have : {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 in K}
          = {p : α × E | p.2 in D (f p.1) K} := by simp [← differentiable_set_eq_D K hK]
  rw [this]
  simp only [D, mem_iInter, mem_iUnion]
  simp only [ofPred_forall, ofPred_exists]
  refine MeasurableSet.iInter (

Depends on / 依赖: DifferentiableAt, MeasurableSet, MeasurableSet.iInter, MeasurableSet.iUnion, differentiable_set_eq_D, fderiv, iInter, iUnion, mem_iInter, mem_iUnion, ofPred_exists, ofPred_forall
-/
theorem measurableSet_of_differentiableAt_of_isComplete_with_param
    (hf : Continuous f.uncurry) {K : Set (E ->L[𝕜] F)} (hK : IsComplete K) :
    MeasurableSet {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 in K} := by
  have : {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 in K}
          = {p : α × E | p.2 in D (f p.1) K} := by simp [← differentiable_set_eq_D K hK]
  rw [this]
  simp only [D, mem_iInter, mem_iUnion]
  simp only [ofPred_forall, ofPred_exists]
  refine MeasurableSet.iInter (fun _ => ?_)
  refine MeasurableSet.iUnion (fun _ => ?_)
  refine MeasurableSet.iInter (fun _ => ?_)
  refine MeasurableSet.iInter (fun _ => ?_)
  refine MeasurableSet.iInter (fun _ => ?_)
  refine MeasurableSet.iInter (fun _ => ?_)
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  exact (isOpen_B_with_param hf K).measurableSet

variable (𝕜)
variable [CompleteSpace F]

/--
theorem `measurableSet_of_differentiableAt_with_param` / 定理 `measurableSet_of_differentiableAt_with_param`

English:
theorem measurableSet_of_differentiableAt_with_param
  given: (hf : Continuous f.uncurry)
  proof: by
  have : IsComplete (univ : Set (E ->L[𝕜] F)) := isComplete_univ
  convert! measurableSet_of_differentiableAt_of_isComplete_with_param hf this
  simp

中文:
定理 measurableSet_of_differentiableAt_with_param
  条件: (hf : Continuous f.uncurry)
  证明: by
  have : IsComplete (univ : Set (E ->L[𝕜] F)) := isComplete_univ
  convert! measurableSet_of_differentiableAt_of_isComplete_with_param hf this
  simp

Depends on / 依赖: IsComplete, convert, isComplete_univ, measurableSet_of_differentiableAt_of_isComplete_with_param
-/
theorem measurableSet_of_differentiableAt_with_param (hf : Continuous f.uncurry) :
    MeasurableSet {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2} := by
  have : IsComplete (univ : Set (E ->L[𝕜] F)) := isComplete_univ
  convert! measurableSet_of_differentiableAt_of_isComplete_with_param hf this
  simp

/--
theorem `measurable_fderiv_with_param` / 定理 `measurable_fderiv_with_param`

English:
theorem measurable_fderiv_with_param
  given: (hf : Continuous f.uncurry)
  proof: by
  refine measurable_of_isClosed (fun s hs => ?_)
  have :
    (fun (p : α × E) => fderiv 𝕜 (f p.1) p.2) ⁻¹' s =
      {p | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 in s } union
        { p | ¬DifferentiableAt 𝕜 (f p.1) p.2} inter { _p | (0 : E ->L[𝕜] F) in s} :=
    Set.ext (fun x =>

中文:
定理 measurable_fderiv_with_param
  条件: (hf : Continuous f.uncurry)
  证明: by
  refine measurable_of_isClosed (fun s hs => ?_)
  have :
    (fun (p : α × E) => fderiv 𝕜 (f p.1) p.2) ⁻¹' s =
      {p | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 in s } union
        { p | ¬DifferentiableAt 𝕜 (f p.1) p.2} inter { _p | (0 : E ->L[𝕜] F) in s} :=
    Set.ext (fun x =>

Depends on / 依赖: DifferentiableAt, MeasurableSet, MeasurableSet.const, Set.ext, compl.inter, fderiv, fderiv_mem_iff, hs.isComplete, isComplete, measurableSet_of_differentiableAt_of_isComplete_with_param, measurableSet_of_differentiableAt_with_param, measurable_of_isClosed, mem_preimage, mem_preimage.trans
-/
theorem measurable_fderiv_with_param (hf : Continuous f.uncurry) :
    Measurable (fun (p : α × E) => fderiv 𝕜 (f p.1) p.2) := by
  refine measurable_of_isClosed (fun s hs => ?_)
  have :
    (fun (p : α × E) => fderiv 𝕜 (f p.1) p.2) ⁻¹' s =
      {p | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 in s } union
        { p | ¬DifferentiableAt 𝕜 (f p.1) p.2} inter { _p | (0 : E ->L[𝕜] F) in s} :=
    Set.ext (fun x => mem_preimage.trans fderiv_mem_iff)
  rw [this]
  exact
    (measurableSet_of_differentiableAt_of_isComplete_with_param hf hs.isComplete).union
      ((measurableSet_of_differentiableAt_with_param _ hf).compl.inter (MeasurableSet.const _))

/--
theorem `measurable_fderiv_apply_const_with_param` / 定理 `measurable_fderiv_apply_const_with_param`

English:
theorem measurable_fderiv_apply_const_with_param
  statement: [MeasurableSpace F] [BorelSpace F]
  proof: (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv_with_param 𝕜 hf)

中文:
定理 measurable_fderiv_apply_const_with_param
  结论: [MeasurableSpace F] [BorelSpace F]
  证明: (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv_with_param 𝕜 hf)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.measurable_apply, measurable_apply, measurable_fderiv_with_param
-/
theorem measurable_fderiv_apply_const_with_param [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f.uncurry) (y : E) :
    Measurable (fun (p : α × E) => fderiv 𝕜 (f p.1) p.2 y) :=
  (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv_with_param 𝕜 hf)

variable {𝕜}

/--
theorem `measurable_deriv_with_param` / 定理 `measurable_deriv_with_param`

English:
theorem measurable_deriv_with_param
  statement: [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
  proof: by
  simpa only [fderiv_apply_one_eq_deriv] using measurable_fderiv_apply_const_with_param 𝕜 hf 1

中文:
定理 measurable_deriv_with_param
  结论: [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
  证明: by
  simpa only [fderiv_apply_one_eq_deriv] using measurable_fderiv_apply_const_with_param 𝕜 hf 1

Depends on / 依赖: fderiv_apply_one_eq_deriv, measurable_fderiv_apply_const_with_param
-/
theorem measurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] {f : α -> 𝕜 -> F} (hf : Continuous f.uncurry) :
    Measurable (fun (p : α × 𝕜) => deriv (f p.1) p.2) := by
  simpa only [fderiv_apply_one_eq_deriv] using measurable_fderiv_apply_const_with_param 𝕜 hf 1

/--
theorem `stronglyMeasurable_deriv_with_param` / 定理 `stronglyMeasurable_deriv_with_param`

English:
theorem stronglyMeasurable_deriv_with_param
  statement: [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
  proof: by
  borelize F
  rcases h.out with hα | hF
  · have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
    apply stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_deriv_with_param hf, ?_⟩
    have : range (fun (p : α × 𝕜) => deriv (f p.1) p.2)
        subseteq closure (Submodule.span 𝕜 (range f.u

中文:
定理 stronglyMeasurable_deriv_with_param
  结论: [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
  证明: by
  borelize F
  rcases h.out with hα | hF
  · have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
    apply stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_deriv_with_param hf, ?_⟩
    have : range (fun (p : α × 𝕜) => deriv (f p.1) p.2)
        subseteq closure (Submodule.span 𝕜 (range f.u

Depends on / 依赖: ProperSpace, Submodule, Submodule.span, borelize, closure, dense_univ, f.uncurry, h.out, image_univ, measurable_deriv_with_param, mem_range_self, of_locallyCompactSpace, range_deriv_subset_closure_span_image, stronglyMeasurable_iff_measurable_separable, subseteq, uncurry
-/
theorem stronglyMeasurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] [h : SecondCountableTopologyEither α F]
    {f : α -> 𝕜 -> F} (hf : Continuous f.uncurry) :
    StronglyMeasurable (fun (p : α × 𝕜) => deriv (f p.1) p.2) := by
  borelize F
  rcases h.out with hα | hF
  · have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
    apply stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_deriv_with_param hf, ?_⟩
    have : range (fun (p : α × 𝕜) => deriv (f p.1) p.2)
        subseteq closure (Submodule.span 𝕜 (range f.uncurry)) := by
      rintro - ⟨p, rfl⟩
      have A : deriv (f p.1) p.2 in closure (Submodule.span 𝕜 (range (f p.1))) := by
        rw [← image_univ]
        apply range_deriv_subset_closure_span_image _ dense_univ (mem_range_self _)
      have B : range (f p.1) subseteq range (f.uncurry) := by
        rintro - ⟨x, rfl⟩
        exact mem_range_self (p.1, x)
      exact closure_mono (Submodule.span_mono B) A
    exact (isSeparable_range hf).span.closure.mono this
  · exact (measurable_deriv_with_param hf).stronglyMeasurable

/--
theorem `aemeasurable_deriv_with_param` / 定理 `aemeasurable_deriv_with_param`

English:
theorem aemeasurable_deriv_with_param
  statement: [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
  proof: (measurable_deriv_with_param hf).aemeasurable

中文:
定理 aemeasurable_deriv_with_param
  结论: [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
  证明: (measurable_deriv_with_param hf).aemeasurable

Depends on / 依赖: aemeasurable, measurable_deriv_with_param
-/
theorem aemeasurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] {f : α -> 𝕜 -> F} (hf : Continuous f.uncurry) (μ : Measure (α × 𝕜)) :
    AEMeasurable (fun (p : α × 𝕜) => deriv (f p.1) p.2) μ :=
  (measurable_deriv_with_param hf).aemeasurable

/--
theorem `aestronglyMeasurable_deriv_with_param` / 定理 `aestronglyMeasurable_deriv_with_param`

English:
theorem aestronglyMeasurable_deriv_with_param
  statement: [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
  proof: (stronglyMeasurable_deriv_with_param hf).aestronglyMeasurable

中文:
定理 aestronglyMeasurable_deriv_with_param
  结论: [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
  证明: (stronglyMeasurable_deriv_with_param hf).aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, stronglyMeasurable_deriv_with_param
-/
theorem aestronglyMeasurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] [SecondCountableTopologyEither α F]
    {f : α -> 𝕜 -> F} (hf : Continuous f.uncurry) (μ : Measure (α × 𝕜)) :
    AEStronglyMeasurable (fun (p : α × 𝕜) => deriv (f p.1) p.2) μ :=
  (stronglyMeasurable_deriv_with_param hf).aestronglyMeasurable

end WithParam
