/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Smoothness of series

We show that series of functions are differentiable, or smooth, when each individual
function in the series is and additionally suitable uniform summable bounds are satisfied.

More specifically,
* `differentiable_tsum` ensures that a series of differentiable functions is differentiable.
* `contDiff_tsum` ensures that a series of `C^n` functions is `C^n`.

We also give versions of these statements which are localized to a set.
-/

public section


open Set Metric TopologicalSpace Function Asymptotics Filter

open scoped Topology NNReal

variable {α β 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [CompleteSpace F] {u : α -> Real}

/-! ### Differentiability -/

variable [NormedSpace 𝕜 F]
variable {f : α -> E -> F} {f' : α -> E -> E ->L[𝕜] F} {g : α -> 𝕜 -> F} {g' : α -> 𝕜 -> F} {v : Nat -> α -> Real}
  {s : Set E} {t : Set 𝕜} {x₀ x : E} {y₀ y : 𝕜} {N : Nat∞}

/--
theorem `summable_of_summable_hasFDerivAt_of_isPreconnected` / 定理 `summable_of_summable_hasFDerivAt_of_isPreconnected`

English:
theorem summable_of_summable_hasFDerivAt_of_isPreconnected
  statement: (hu : Summable u) (hs : IsOpen s)
  proof: by
  have := Classical.decEq α
  rw [summable_iff_cauchySeq_finset] at hf0 ⊢
  have A : UniformCauchySeqOn (fun t : Finset α => fun x => ∑ i in t, f' i x) atTop s :=
    (tendstoUniformlyOn_tsum hu hf').uniformCauchySeqOn
  refine cauchy_map_of_uniformCauchySeqOn_fderiv (f := fun t x => ∑ i in t, f 

中文:
定理 summable_of_summable_hasFDerivAt_of_isPreconnected
  结论: (hu : Summable u) (hs : IsOpen s)
  证明: by
  have := Classical.decEq α
  rw [summable_iff_cauchySeq_finset] at hf0 ⊢
  have A : UniformCauchySeqOn (fun t : Finset α => fun x => ∑ i in t, f' i x) atTop s :=
    (tendstoUniformlyOn_tsum hu hf').uniformCauchySeqOn
  refine cauchy_map_of_uniformCauchySeqOn_fderiv (f := fun t x => ∑ i in t, f 

Depends on / 依赖: Classical, Classical.decEq, Finset, HasFDerivAt, HasFDerivAt.fun_sum, UniformCauchySeqOn, cauchy_map_of_uniformCauchySeqOn_fderiv, fun_sum, summable_iff_cauchySeq_finset, tendstoUniformlyOn_tsum, uniformCauchySeqOn
-/
theorem summable_of_summable_hasFDerivAt_of_isPreconnected (hu : Summable u) (hs : IsOpen s)
    (h's : IsPreconnected s) (hf : forall n x, x in s -> HasFDerivAt (f n) (f' n x) x)
    (hf' : forall n x, x in s -> ‖f' n x‖ <= u n) (hx₀ : x₀ in s) (hf0 : Summable (f · x₀))
    (hx : x in s) : Summable fun n => f n x := by
  have := Classical.decEq α
  rw [summable_iff_cauchySeq_finset] at hf0 ⊢
  have A : UniformCauchySeqOn (fun t : Finset α => fun x => ∑ i in t, f' i x) atTop s :=
    (tendstoUniformlyOn_tsum hu hf').uniformCauchySeqOn
  refine cauchy_map_of_uniformCauchySeqOn_fderiv (f := fun t x => ∑ i in t, f i x)
    hs h's A (fun t y hy => ?_) hx₀ hx hf0
  exact HasFDerivAt.fun_sum fun i _ => hf i y hy

/--
theorem `summable_of_summable_hasDerivAt_of_isPreconnected` / 定理 `summable_of_summable_hasDerivAt_of_isPreconnected`

English:
theorem summable_of_summable_hasDerivAt_of_isPreconnected
  statement: (hu : Summable u) (ht : IsOpen t)
  proof: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine summable_of_summable_hasFDerivAt_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
  simpa

中文:
定理 summable_of_summable_hasDerivAt_of_isPreconnected
  结论: (hu : Summable u) (ht : IsOpen t)
  证明: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine summable_of_summable_hasFDerivAt_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
  simpa

Depends on / 依赖: hasDerivAt_iff_hasFDerivAt, simp_rw, summable_of_summable_hasFDerivAt_of_isPreconnected
-/
theorem summable_of_summable_hasDerivAt_of_isPreconnected (hu : Summable u) (ht : IsOpen t)
    (h't : IsPreconnected t) (hg : forall n y, y in t -> HasDerivAt (g n) (g' n y) y)
    (hg' : forall n y, y in t -> ‖g' n y‖ <= u n) (hy₀ : y₀ in t) (hg0 : Summable (g · y₀))
    (hy : y in t) : Summable fun n => g n y := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine summable_of_summable_hasFDerivAt_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
  simpa

/--
theorem `hasFDerivAt_tsum_of_isPreconnected` / 定理 `hasFDerivAt_tsum_of_isPreconnected`

English:
theorem hasFDerivAt_tsum_of_isPreconnected
  statement: (hu : Summable u) (hs : IsOpen s)
  proof: by
  have A :
    forall x : E, x in s -> Tendsto (fun t : Finset α => ∑ n in t, f n x) atTop (𝓝 (∑' n, f n x)) := by
    intro y hy
    apply Summable.hasSum
    exact summable_of_summable_hasFDerivAt_of_isPreconnected hu hs h's hf hf' hx₀ hf0 hy
  refine hasFDerivAt_of_tendstoUniformlyOn hs (tends

中文:
定理 hasFDerivAt_tsum_of_isPreconnected
  结论: (hu : Summable u) (hs : IsOpen s)
  证明: by
  have A :
    forall x : E, x in s -> Tendsto (fun t : Finset α => ∑ n in t, f n x) atTop (𝓝 (∑' n, f n x)) := by
    intro y hy
    apply Summable.hasSum
    exact summable_of_summable_hasFDerivAt_of_isPreconnected hu hs h's hf hf' hx₀ hf0 hy
  refine hasFDerivAt_of_tendstoUniformlyOn hs (tends

Depends on / 依赖: Finset, HasFDerivAt, HasFDerivAt.fun_sum, Summable, Summable.hasSum, Tendsto, fun_sum, hasFDerivAt_of_tendstoUniformlyOn, hasSum, summable_of_summable_hasFDerivAt_of_isPreconnected, tendstoUniformlyOn_tsum
-/
theorem hasFDerivAt_tsum_of_isPreconnected (hu : Summable u) (hs : IsOpen s)
    (h's : IsPreconnected s) (hf : forall n x, x in s -> HasFDerivAt (f n) (f' n x) x)
    (hf' : forall n x, x in s -> ‖f' n x‖ <= u n) (hx₀ : x₀ in s) (hf0 : Summable fun n => f n x₀)
    (hx : x in s) : HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  have A :
    forall x : E, x in s -> Tendsto (fun t : Finset α => ∑ n in t, f n x) atTop (𝓝 (∑' n, f n x)) := by
    intro y hy
    apply Summable.hasSum
    exact summable_of_summable_hasFDerivAt_of_isPreconnected hu hs h's hf hf' hx₀ hf0 hy
  refine hasFDerivAt_of_tendstoUniformlyOn hs (tendstoUniformlyOn_tsum hu hf')
    (fun t y hy => ?_) A hx
  exact HasFDerivAt.fun_sum fun n _ => hf n y hy

/--
theorem `hasDerivAt_tsum_of_isPreconnected` / 定理 `hasDerivAt_tsum_of_isPreconnected`

English:
theorem hasDerivAt_tsum_of_isPreconnected
  statement: (hu : Summable u) (ht : IsOpen t)
  proof: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg ⊢
  convert! hasFDerivAt_tsum_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
· exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 F 1).map_tsum
      .of_norm_bounded hu fun n => hg' n y hy
  · simpa

中文:
定理 hasDerivAt_tsum_of_isPreconnected
  结论: (hu : Summable u) (ht : IsOpen t)
  证明: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg ⊢
  convert! hasFDerivAt_tsum_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
· exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 F 1).map_tsum
      .of_norm_bounded hu fun n => hg' n y hy
  · simpa

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.smulRightL, convert, hasDerivAt_iff_hasFDerivAt, hasFDerivAt_tsum_of_isPreconnected, map_tsum, of_norm_bounded, simp_rw, smulRightL
-/
theorem hasDerivAt_tsum_of_isPreconnected (hu : Summable u) (ht : IsOpen t)
    (h't : IsPreconnected t) (hg : forall n y, y in t -> HasDerivAt (g n) (g' n y) y)
    (hg' : forall n y, y in t -> ‖g' n y‖ <= u n) (hy₀ : y₀ in t) (hg0 : Summable fun n => g n y₀)
    (hy : y in t) : HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg ⊢
  convert! hasFDerivAt_tsum_of_isPreconnected hu ht h't hg ?_ hy₀ hg0 hy
· exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 F 1).map_tsum
      .of_norm_bounded hu fun n => hg' n y hy
  · simpa

/--
theorem `summable_of_summable_hasFDerivAt` / 定理 `summable_of_summable_hasFDerivAt`

English:
theorem summable_of_summable_hasFDerivAt
  statement: (hu : Summable u)
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  exact summable_of_summable_hasFDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

中文:
定理 summable_of_summable_hasFDerivAt
  结论: (hu : Summable u)
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  exact summable_of_summable_hasFDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, NormedSpace, NormedSpace.restrictScalars, RCLike, isOpen_univ, isPreconnected_univ, mem_univ, rclike, restrictScalars, summable_of_summable_hasFDerivAt_of_isPreconnected
-/
theorem summable_of_summable_hasFDerivAt (hu : Summable u)
    (hf : forall n x, HasFDerivAt (f n) (f' n x) x) (hf' : forall n x, ‖f' n x‖ <= u n)
    (hf0 : Summable fun n => f n x₀) (x : E) : Summable fun n => f n x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  exact summable_of_summable_hasFDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

/--
theorem `summable_of_summable_hasDerivAt` / 定理 `summable_of_summable_hasDerivAt`

English:
theorem summable_of_summable_hasDerivAt
  statement: (hu : Summable u)
  proof: by
  exact summable_of_summable_hasDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hg n x) (fun n x _ => hg' n x) (mem_univ _) hg0 (mem_univ _)

中文:
定理 summable_of_summable_hasDerivAt
  结论: (hu : Summable u)
  证明: by
  exact summable_of_summable_hasDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hg n x) (fun n x _ => hg' n x) (mem_univ _) hg0 (mem_univ _)

Depends on / 依赖: isOpen_univ, isPreconnected_univ, mem_univ, summable_of_summable_hasDerivAt_of_isPreconnected
-/
theorem summable_of_summable_hasDerivAt (hu : Summable u)
    (hg : forall n y, HasDerivAt (g n) (g' n y) y) (hg' : forall n y, ‖g' n y‖ <= u n)
    (hg0 : Summable fun n => g n y₀) (y : 𝕜) : Summable fun n => g n y := by
  exact summable_of_summable_hasDerivAt_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hg n x) (fun n x _ => hg' n x) (mem_univ _) hg0 (mem_univ _)

/--
theorem `hasFDerivAt_tsum` / 定理 `hasFDerivAt_tsum`

English:
theorem hasFDerivAt_tsum
  statement: (hu : Summable u) (hf : forall n x, HasFDerivAt (f n) (f' n x) x)
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  exact hasFDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

中文:
定理 hasFDerivAt_tsum
  结论: (hu : Summable u) (hf : 对任意 n x, HasFDerivAt (f n) (f' n x) x)
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  exact hasFDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, NormedSpace, NormedSpace.restrictScalars, RCLike, hasFDerivAt_tsum_of_isPreconnected, isOpen_univ, isPreconnected_univ, mem_univ, rclike, restrictScalars
-/
theorem hasFDerivAt_tsum (hu : Summable u) (hf : forall n x, HasFDerivAt (f n) (f' n x) x)
    (hf' : forall n x, ‖f' n x‖ <= u n) (hf0 : Summable fun n => f n x₀) (x : E) :
    HasFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 _
  exact hasFDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n x _ => hf n x) (fun n x _ => hf' n x) (mem_univ _) hf0 (mem_univ _)

/--
theorem `hasDerivAt_tsum` / 定理 `hasDerivAt_tsum`

English:
theorem hasDerivAt_tsum
  statement: (hu : Summable u) (hg : forall n y, HasDerivAt (g n) (g' n y) y)
  proof: by
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n y _ => hg n y) (fun n y _ => hg' n y) (mem_univ _) hg0 (mem_univ _)

中文:
定理 hasDerivAt_tsum
  结论: (hu : Summable u) (hg : 对任意 n y, HasDerivAt (g n) (g' n y) y)
  证明: by
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n y _ => hg n y) (fun n y _ => hg' n y) (mem_univ _) hg0 (mem_univ _)

Depends on / 依赖: hasDerivAt_tsum_of_isPreconnected, isOpen_univ, isPreconnected_univ, mem_univ
-/
theorem hasDerivAt_tsum (hu : Summable u) (hg : forall n y, HasDerivAt (g n) (g' n y) y)
    (hg' : forall n y, ‖g' n y‖ <= u n) (hg0 : Summable fun n => g n y₀) (y : 𝕜) :
    HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := by
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_univ isPreconnected_univ
    (fun n y _ => hg n y) (fun n y _ => hg' n y) (mem_univ _) hg0 (mem_univ _)

/--
theorem `differentiable_tsum` / 定理 `differentiable_tsum`

English:
theorem differentiable_tsum
  statement: (hu : Summable u) (hf : forall n x, HasFDerivAt (f n) (f' n x) x)
  proof: by
  by_cases! h : exists x₀, Summable fun n => f n x₀
  · rcases h with ⟨x₀, hf0⟩
    intro x
    exact (hasFDerivAt_tsum hu hf hf' hf0 x).differentiableAt
  · have : (fun x => ∑' n, f n x) = 0 := by ext1 x; exact tsum_eq_zero_of_not_summable (h x)
    rw [this]
    exact differentiable_const 0

中文:
定理 differentiable_tsum
  结论: (hu : Summable u) (hf : 对任意 n x, HasFDerivAt (f n) (f' n x) x)
  证明: by
  by_cases! h : exists x₀, Summable fun n => f n x₀
  · rcases h with ⟨x₀, hf0⟩
    intro x
    exact (hasFDerivAt_tsum hu hf hf' hf0 x).differentiableAt
  · have : (fun x => ∑' n, f n x) = 0 := by ext1 x; exact tsum_eq_zero_of_not_summable (h x)
    rw [this]
    exact differentiable_const 0

Depends on / 依赖: Summable, differentiableAt, differentiable_const, hasFDerivAt_tsum, tsum_eq_zero_of_not_summable
-/
theorem differentiable_tsum (hu : Summable u) (hf : forall n x, HasFDerivAt (f n) (f' n x) x)
    (hf' : forall n x, ‖f' n x‖ <= u n) : Differentiable 𝕜 fun y => ∑' n, f n y := by
  by_cases! h : exists x₀, Summable fun n => f n x₀
  · rcases h with ⟨x₀, hf0⟩
    intro x
    exact (hasFDerivAt_tsum hu hf hf' hf0 x).differentiableAt
  · have : (fun x => ∑' n, f n x) = 0 := by ext1 x; exact tsum_eq_zero_of_not_summable (h x)
    rw [this]
    exact differentiable_const 0

/--
theorem `differentiable_tsum'` / 定理 `differentiable_tsum'`

English:
theorem differentiable_tsum'
  statement: (hu : Summable u) (hg : forall n y, HasDerivAt (g n) (g' n y) y)
  proof: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine differentiable_tsum hu hg ?_
  simpa

中文:
定理 differentiable_tsum'
  结论: (hu : Summable u) (hg : 对任意 n y, HasDerivAt (g n) (g' n y) y)
  证明: by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine differentiable_tsum hu hg ?_
  simpa

Depends on / 依赖: differentiable_tsum, hasDerivAt_iff_hasFDerivAt, simp_rw
-/
theorem differentiable_tsum' (hu : Summable u) (hg : forall n y, HasDerivAt (g n) (g' n y) y)
    (hg' : forall n y, ‖g' n y‖ <= u n) : Differentiable 𝕜 fun z => ∑' n, g n z := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hg
  refine differentiable_tsum hu hg ?_
  simpa

/--
theorem `fderiv_tsum_apply` / 定理 `fderiv_tsum_apply`

English:
theorem fderiv_tsum_apply
  statement: (hu : Summable u) (hf : forall n, Differentiable 𝕜 (f n))
  proof: (hasFDerivAt_tsum hu (fun n x => (hf n x).hasFDerivAt) hf' hf0 _).fderiv

中文:
定理 fderiv_tsum_apply
  结论: (hu : Summable u) (hf : 对任意 n, Differentiable 𝕜 (f n))
  证明: (hasFDerivAt_tsum hu (fun n x => (hf n x).hasFDerivAt) hf' hf0 _).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hasFDerivAt_tsum
-/
theorem fderiv_tsum_apply (hu : Summable u) (hf : forall n, Differentiable 𝕜 (f n))
    (hf' : forall n x, ‖fderiv 𝕜 (f n) x‖ <= u n) (hf0 : Summable fun n => f n x₀) (x : E) :
    fderiv 𝕜 (fun y => ∑' n, f n y) x = ∑' n, fderiv 𝕜 (f n) x :=
  (hasFDerivAt_tsum hu (fun n x => (hf n x).hasFDerivAt) hf' hf0 _).fderiv

/--
theorem `deriv_tsum_apply` / 定理 `deriv_tsum_apply`

English:
theorem deriv_tsum_apply
  statement: (hu : Summable u) (hg : forall n, Differentiable 𝕜 (g n))
  proof: (hasDerivAt_tsum hu (fun n y => (hg n y).hasDerivAt) hg' hg0 _).deriv

中文:
定理 deriv_tsum_apply
  结论: (hu : Summable u) (hg : 对任意 n, Differentiable 𝕜 (g n))
  证明: (hasDerivAt_tsum hu (fun n y => (hg n y).hasDerivAt) hg' hg0 _).deriv

Depends on / 依赖: hasDerivAt, hasDerivAt_tsum
-/
theorem deriv_tsum_apply (hu : Summable u) (hg : forall n, Differentiable 𝕜 (g n))
    (hg' : forall n y, ‖deriv (g n) y‖ <= u n) (hg0 : Summable fun n => g n y₀) (y : 𝕜) :
    deriv (fun z => ∑' n, g n z) y = ∑' n, deriv (g n) y :=
  (hasDerivAt_tsum hu (fun n y => (hg n y).hasDerivAt) hg' hg0 _).deriv

/--
theorem `fderiv_tsum` / 定理 `fderiv_tsum`

English:
theorem fderiv_tsum
  statement: (hu : Summable u) (hf : forall n, Differentiable 𝕜 (f n))
  proof: by
  ext1 x
  exact fderiv_tsum_apply hu hf hf' hf0 x

中文:
定理 fderiv_tsum
  结论: (hu : Summable u) (hf : 对任意 n, Differentiable 𝕜 (f n))
  证明: by
  ext1 x
  exact fderiv_tsum_apply hu hf hf' hf0 x

Depends on / 依赖: fderiv_tsum_apply
-/
theorem fderiv_tsum (hu : Summable u) (hf : forall n, Differentiable 𝕜 (f n))
    (hf' : forall n x, ‖fderiv 𝕜 (f n) x‖ <= u n) (hf0 : Summable fun n => f n x₀) :
    (fderiv 𝕜 fun y => ∑' n, f n y) = fun x => ∑' n, fderiv 𝕜 (f n) x := by
  ext1 x
  exact fderiv_tsum_apply hu hf hf' hf0 x

/--
theorem `deriv_tsum` / 定理 `deriv_tsum`

English:
theorem deriv_tsum
  statement: (hu : Summable u) (hg : forall n, Differentiable 𝕜 (g n))
  proof: by
  ext1 x
  exact deriv_tsum_apply hu hg hg' hg0 x

中文:
定理 deriv_tsum
  结论: (hu : Summable u) (hg : 对任意 n, Differentiable 𝕜 (g n))
  证明: by
  ext1 x
  exact deriv_tsum_apply hu hg hg' hg0 x

Depends on / 依赖: deriv_tsum_apply
-/
theorem deriv_tsum (hu : Summable u) (hg : forall n, Differentiable 𝕜 (g n))
    (hg' : forall n y, ‖deriv (g n) y‖ <= u n) (hg0 : Summable fun n => g n y₀) :
    (deriv fun y => ∑' n, g n y) = fun y => ∑' n, deriv (g n) y := by
  ext1 x
  exact deriv_tsum_apply hu hg hg' hg0 x

/-! ### Higher smoothness -/

/--
theorem `iteratedFDeriv_tsum` / 定理 `iteratedFDeriv_tsum`

English:
theorem iteratedFDeriv_tsum
  statement: (hf : forall i, ContDiff 𝕜 N (f i))
  proof: by
  induction k with
  | zero =>
    ext1 x
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k IH =>
    have h'k : (k : Nat∞) < N := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Nat.lt_succ_self _)) hk
    have A : S

中文:
定理 iteratedFDeriv_tsum
  结论: (hf : 对任意 i, ContDiff 𝕜 N (f i))
  证明: by
  induction k with
  | zero =>
    ext1 x
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k IH =>
    have h'k : (k : Nat∞) < N := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Nat.lt_succ_self _)) hk
    have A : S

Depends on / 依赖: Nat.lt_succ_self, Summable, WithTop, WithTop.coe_lt_coe, coe_lt_coe, continuousMultilinearCurryFin0, differentiable_iteratedFD, fderiv_tsum, iteratedFDeriv, iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_zero_eq_comp, k.le, lt_of_lt_of_le, lt_succ_self, map_tsum, of_norm_bounded, simp_rw, symm.toContinuousLinearEquiv.map_tsum, toContinuousLinearEquiv
-/
theorem iteratedFDeriv_tsum (hf : forall i, ContDiff 𝕜 N (f i))
    (hv : forall k : Nat, (k : Nat∞) <= N -> Summable (v k))
    (h'f : forall (k : Nat) (i : α) (x : E), (k : Nat∞) <= N -> ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i) {k : Nat}
    (hk : (k : Nat∞) <= N) :
    (iteratedFDeriv 𝕜 k fun y => ∑' n, f n y) = fun x => ∑' n, iteratedFDeriv 𝕜 k (f n) x := by
  induction k with
  | zero =>
    ext1 x
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k IH =>
    have h'k : (k : Nat∞) < N := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Nat.lt_succ_self _)) hk
    have A : Summable fun n => iteratedFDeriv 𝕜 k (f n) 0 :=
      .of_norm_bounded (hv k h'k.le) fun n => h'f k n 0 h'k.le
    simp_rw [iteratedFDeriv_succ_eq_comp_left, IH h'k.le]
    rw [fderiv_tsum (hv _ hk) (fun n => (hf n).differentiable_iteratedFDeriv
        (mod_cast h'k)) _ A]
    · ext1 x
      exact (continuousMultilinearCurryLeftEquiv 𝕜
        (fun _ : Fin (k + 1) => E) F).symm.toContinuousLinearEquiv.map_tsum
    · intro n x
      simpa only [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_map, comp_apply]
        using h'f k.succ n x hk

/--
theorem `iteratedFDeriv_tsum_apply` / 定理 `iteratedFDeriv_tsum_apply`

English:
theorem iteratedFDeriv_tsum_apply
  statement: (hf : forall i, ContDiff 𝕜 N (f i))
  proof: by
  rw [iteratedFDeriv_tsum hf hv h'f hk]

中文:
定理 iteratedFDeriv_tsum_apply
  结论: (hf : 对任意 i, ContDiff 𝕜 N (f i))
  证明: by
  rw [iteratedFDeriv_tsum hf hv h'f hk]

Depends on / 依赖: iteratedFDeriv_tsum
-/
theorem iteratedFDeriv_tsum_apply (hf : forall i, ContDiff 𝕜 N (f i))
    (hv : forall k : Nat, (k : Nat∞) <= N -> Summable (v k))
    (h'f : forall (k : Nat) (i : α) (x : E), (k : Nat∞) <= N -> ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i) {k : Nat}
    (hk : (k : Nat∞) <= N) (x : E) :
    iteratedFDeriv 𝕜 k (fun y => ∑' n, f n y) x = ∑' n, iteratedFDeriv 𝕜 k (f n) x := by
  rw [iteratedFDeriv_tsum hf hv h'f hk]

/--
theorem `contDiff_tsum` / 定理 `contDiff_tsum`

English:
theorem contDiff_tsum
  statement: (hf : forall i, ContDiff 𝕜 N (f i)) (hv : forall k : Nat, (k : Nat∞) <= N -> Summable (v k))
  proof: by
  rw [contDiff_iff_continuous_differentiable]
  constructor
  · intro m hm
    rw [iteratedFDeriv_tsum hf hv h'f hm]
    refine continuous_tsum ?_ (hv m hm) ?_
    · intro i
      exact ContDiff.continuous_iteratedFDeriv (mod_cast hm) (hf i)
    · intro n x
      exact h'f _ _ _ hm
  · intro m hm

中文:
定理 contDiff_tsum
  结论: (hf : 对任意 i, ContDiff 𝕜 N (f i)) (hv : 对任意 k : 自然数, (k : 自然数∞) <= N -> Summable (v k))
  证明: by
  rw [contDiff_iff_continuous_differentiable]
  constructor
  · intro m hm
    rw [iteratedFDeriv_tsum hf hv h'f hm]
    refine continuous_tsum ?_ (hv m hm) ?_
    · intro i
      exact ContDiff.continuous_iteratedFDeriv (mod_cast hm) (hf i)
    · intro n x
      exact h'f _ _ _ hm
  · intro m hm

Depends on / 依赖: ContDiff, ContDiff.continuous_iteratedFDeriv, ENat.natCast_add, ENat.natCast_one, HasFDerivAt, Order.add_one_le_of_lt, add_one_le_of_lt, contDiff_iff_continuous_differentiable, continuous_iteratedFDeriv, continuous_tsum, fderiv, hm.le, iterat, iteratedFDeriv, iteratedFDeriv_tsum, mod_cast, natCast_add, natCast_one
-/
theorem contDiff_tsum (hf : forall i, ContDiff 𝕜 N (f i)) (hv : forall k : Nat, (k : Nat∞) <= N -> Summable (v k))
    (h'f : forall (k : Nat) (i : α) (x : E), k <= N -> ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i) :
    ContDiff 𝕜 N fun x => ∑' i, f i x := by
  rw [contDiff_iff_continuous_differentiable]
  constructor
  · intro m hm
    rw [iteratedFDeriv_tsum hf hv h'f hm]
    refine continuous_tsum ?_ (hv m hm) ?_
    · intro i
      exact ContDiff.continuous_iteratedFDeriv (mod_cast hm) (hf i)
    · intro n x
      exact h'f _ _ _ hm
  · intro m hm
    have h'm : ((m + 1 : Nat) : Nat∞) <= N := by
      simpa only [ENat.natCast_add, ENat.natCast_one] using Order.add_one_le_of_lt hm
    rw [iteratedFDeriv_tsum hf hv h'f hm.le]
    have A n x : HasFDerivAt (iteratedFDeriv 𝕜 m (f n)) (fderiv 𝕜 (iteratedFDeriv 𝕜 m (f n)) x) x :=
      (ContDiff.differentiable_iteratedFDeriv (mod_cast hm)
        (hf n)).differentiableAt.hasFDerivAt
    refine differentiable_tsum (hv _ h'm) A fun n x => ?_
    rw [fderiv_iteratedFDeriv]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]
    exact h'f _ _ _ h'm

/--
theorem `contDiff_tsum_of_eventually` / 定理 `contDiff_tsum_of_eventually`

English:
theorem contDiff_tsum_of_eventually
  statement: (hf : forall i, ContDiff 𝕜 N (f i))
  proof: by
  refine contDiff_iff_forall_nat_le.2 fun m hm => ?_
  let t : Set α :=
    { i : α | ¬forall k : Nat, k in Finset.range (m + 1) -> forall x, ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i }
  have ht : Set.Finite t :=
    haveI A :
      forallᶠ i in (Filter.cofinite : Filter α),
        forall k : Nat, 

中文:
定理 contDiff_tsum_of_eventually
  结论: (hf : 对任意 i, ContDiff 𝕜 N (f i))
  证明: by
  refine contDiff_iff_forall_nat_le.2 fun m hm => ?_
  let t : Set α :=
    { i : α | ¬forall k : Nat, k in Finset.range (m + 1) -> forall x, ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i }
  have ht : Set.Finite t :=
    haveI A :
      forallᶠ i in (Filter.cofinite : Filter α),
        forall k : Nat, 

Depends on / 依赖: Filter, Filter.cofinite, Finite, Finset, Finset.mem_range_succ_iff, Finset.range, Set.Finite, WithTop, WithTop.coe_le_coe, coe_le_coe, cofinite, contDiff_iff_forall_nat_le, eventual, eventually_all_finset, iteratedFDeriv, mem_range_succ_iff
-/
theorem contDiff_tsum_of_eventually (hf : forall i, ContDiff 𝕜 N (f i))
    (hv : forall k : Nat, k <= N -> Summable (v k))
    (h'f : forall k : Nat, k <= N ->
      forallᶠ i in (Filter.cofinite : Filter α), forall x : E, ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i) :
    ContDiff 𝕜 N fun x => ∑' i, f i x := by
  refine contDiff_iff_forall_nat_le.2 fun m hm => ?_
  let t : Set α :=
    { i : α | ¬forall k : Nat, k in Finset.range (m + 1) -> forall x, ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i }
  have ht : Set.Finite t :=
    haveI A :
      forallᶠ i in (Filter.cofinite : Filter α),
        forall k : Nat, k in Finset.range (m + 1) -> forall x : E, ‖iteratedFDeriv 𝕜 k (f i) x‖ <= v k i := by
      rw [eventually_all_finset]
      intro i hi
      apply h'f
      simp only [Finset.mem_range_succ_iff] at hi
      exact (WithTop.coe_le_coe.2 hi).trans hm
    eventually_cofinite.2 A
  let T : Finset α := ht.toFinset
  have : (fun x => ∑' i, f i x) = (fun x => ∑ i in T, f i x) +
      fun x => ∑' i : { i // i ∉ T }, f i x := by
    ext1 x
    refine (Summable.sum_add_tsum_subtype_compl ?_ T).symm
    refine .of_norm_bounded_eventually (hv 0 zero_le) ?_
    filter_upwards [h'f 0 zero_le] with i hi
    simpa only [norm_iteratedFDeriv_zero] using hi x
  rw [this]
  apply (ContDiff.sum fun i _ => (hf i).of_le (mod_cast hm)).add
  have h'u : forall k : Nat, (k : Nat∞) <= m -> Summable (v k ∘ ((↑) : { i // i ∉ T } -> α)) := fun k hk =>
    (hv k (hk.trans hm)).subtype _
  refine contDiff_tsum (fun i => (hf i).of_le (mod_cast hm)) h'u ?_
  rintro k ⟨i, hi⟩ x hk
  simp only [t, T, Finite.mem_toFinset, mem_ofPred_eq, Finset.mem_range, not_forall, not_le,
    exists_prop, not_exists, not_and, not_lt] at hi
  exact hi k (Nat.lt_succ_iff.2 (WithTop.coe_le_coe.1 hk)) x
