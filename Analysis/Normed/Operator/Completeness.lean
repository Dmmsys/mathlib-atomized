/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Operators on complete normed spaces

This file contains statements about norms of operators on complete normed spaces, such as a
version of the Banach-Alaoglu theorem (`ContinuousLinearMap.isCompact_image_coe_closedBall`).
-/

@[expose] public section

suppress_compilation

open Bornology Metric Set Real
open Filter hiding map_smul
open scoped NNReal Topology Uniformity

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ E F Fₗ : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup Fₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ]
  {σ₁₂ : 𝕜 ->+* 𝕜₂} (f g : E ->SL[σ₁₂] F)

namespace ContinuousLinearMap

section Completeness

variable {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [RingHomIsometric σ₁₂]

/-- Construct a bundled continuous (semi)linear map from a map `f : E → F` and a proof of the fact
that it belongs to the closure of the image of a bounded set `s : Set (E →SL[σ₁₂] F)` under coercion
to function. Coercion to function of the result is definitionally equal to `f`. -/
@[simps! -fullyApplied apply]
/--
Definition of `ofMemClosureImageCoeBounded` / `ofMemClosureImageCoeBounded` 的定义

English:
definition ofMemClosureImageCoeBounded
  signature: (f : E' -> F) {s : Set (E' ->SL[σ₁₂] F)} (hs : IsBounded s)
  body: by
  -- `f` is a linear map due to `linearMapOfMemClosureRangeCoe`
  refine (linearMapOfMemClosureRangeCoe f ?_).mkContinuousOfExistsBound ?_
  · refine closure_mono (image_subset_iff.2 fun g _ => ?_) hf
    exact ⟨g, rfl⟩
  · -- We need to show that `f` has bounded norm. Choose `C` such that `‖g‖ ≤

中文:
定义 ofMemClosureImageCoeBounded
  签名: (f : E' -> F) {s : Set (E' ->SL[σ₁₂] F)} (hs : IsBounded s)
  定义体: by
  -- `f` is a linear map due to `linearMapOfMemClosureRangeCoe`
  refine (linearMapOfMemClosureRangeCoe f ?_).mkContinuousOfExistsBound ?_
  · refine closure_mono (image_subset_iff.2 fun g _ => ?_) hf
    exact ⟨g, rfl⟩
  · -- We need to show that `f` has bounded norm. Choose `C` such that `‖g‖ ≤
-/
def ofMemClosureImageCoeBounded (f : E' -> F) {s : Set (E' ->SL[σ₁₂] F)} (hs : IsBounded s)
    (hf : f in closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s)) : E' ->SL[σ₁₂] F := by
  -- `f` is a linear map due to `linearMapOfMemClosureRangeCoe`
  refine (linearMapOfMemClosureRangeCoe f ?_).mkContinuousOfExistsBound ?_
  · refine closure_mono (image_subset_iff.2 fun g _ => ?_) hf
    exact ⟨g, rfl⟩
  · -- We need to show that `f` has bounded norm. Choose `C` such that `‖g‖ ≤ C` for all `g ∈ s`.
    rcases isBounded_iff_forall_norm_le.1 hs with ⟨C, hC⟩
    -- Then `‖g x‖ ≤ C * ‖x‖` for all `g ∈ s`, `x : E`, hence `‖f x‖ ≤ C * ‖x‖` for all `x`.
    have : forall x, IsClosed { g : E' -> F | ‖g x‖ <= C * ‖x‖ } := fun x =>
      isClosed_Iic.preimage (@continuous_apply E' (fun _ => F) _ x).norm
    refine ⟨C, fun x => (this x).closure_subset_iff.2 (image_subset_iff.2 fun g hg => ?_) hf⟩
    exact g.le_of_opNorm_le (hC _ hg) _

/-- Let `f : E → F` be a map, let `g : α → E →SL[σ₁₂] F` be a family of continuous (semi)linear maps
that takes values in a bounded set and converges to `f` pointwise along a nontrivial filter. Then
`f` is a continuous (semi)linear map. -/
@[simps! -fullyApplied apply]
/--
Definition of `ofTendstoOfBoundedRange` / `ofTendstoOfBoundedRange` 的定义

English:
definition ofTendstoOfBoundedRange
  signature: {α : Type*} {l : Filter α} [l.NeBot] (f : E' -> F)
  body: ofMemClosureImageCoeBounded f hg mem_closure_of_tendsto hf
Eventually.of_forall fun _ => mem_image_of_mem _ Set.mem_range_self _

中文:
定义 ofTendstoOfBoundedRange
  签名: {α : 类型} {l : Filter α} [l.NeBot] (f : E' -> F)
  定义体: ofMemClosureImageCoeBounded f hg mem_closure_of_tendsto hf
Eventually.of_forall fun _ => mem_image_of_mem _ Set.mem_range_self _

Depends on / 依赖: Eventually, Eventually.of_forall, Set.mem_range_self, mem_closure_of_tendsto, mem_image_of_mem, mem_range_self, ofMemClosureImageCoeBounded, of_forall
-/
def ofTendstoOfBoundedRange {α : Type*} {l : Filter α} [l.NeBot] (f : E' -> F)
    (g : α -> E' ->SL[σ₁₂] F) (hf : Tendsto (fun a x => g a x) l (𝓝 f))
    (hg : IsBounded (Set.range g)) : E' ->SL[σ₁₂] F :=
ofMemClosureImageCoeBounded f hg mem_closure_of_tendsto hf
Eventually.of_forall fun _ => mem_image_of_mem _ Set.mem_range_self _

/--
theorem `tendsto_of_tendsto_pointwise_of_cauchySeq` / 定理 `tendsto_of_tendsto_pointwise_of_cauchySeq`

English:
theorem tendsto_of_tendsto_pointwise_of_cauchySeq
  statement: {f : Nat -> E' ->SL[σ₁₂] F} {g : E' ->SL[σ₁₂] F}
  proof: by
  /- Since `f` is a Cauchy sequence, there exists `b → 0` such that `‖f n - f m‖ ≤ b N` for any
    `m, n ≥ N`. -/
  rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, hb₀, hfb, hb_lim⟩
  simp_rw [dist_eq_norm] at hfb
  -- Since `b → 0`, it suffices to show that `‖f n x - g x‖ ≤ b n * ‖x‖` for all `

中文:
定理 tendsto_of_tendsto_pointwise_of_cauchySeq
  结论: {f : 自然数 -> E' ->SL[σ₁₂] F} {g : E' ->SL[σ₁₂] F}
  证明: by
  /- Since `f` is a Cauchy sequence, there exists `b → 0` such that `‖f n - f m‖ ≤ b N` for any
    `m, n ≥ N`. -/
  rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, hb₀, hfb, hb_lim⟩
  simp_rw [dist_eq_norm] at hfb
  -- Since `b → 0`, it suffices to show that `‖f n x - g x‖ ≤ b n * ‖x‖` for all `
-/
theorem tendsto_of_tendsto_pointwise_of_cauchySeq {f : Nat -> E' ->SL[σ₁₂] F} {g : E' ->SL[σ₁₂] F}
    (hg : Tendsto (fun n x => f n x) atTop (𝓝 g)) (hf : CauchySeq f) : Tendsto f atTop (𝓝 g) := by
  /- Since `f` is a Cauchy sequence, there exists `b → 0` such that `‖f n - f m‖ ≤ b N` for any
    `m, n ≥ N`. -/
  rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, hb₀, hfb, hb_lim⟩
  simp_rw [dist_eq_norm] at hfb
  -- Since `b → 0`, it suffices to show that `‖f n x - g x‖ ≤ b n * ‖x‖` for all `n` and `x`.
  suffices forall n x, ‖f n x - g x‖ <= b n * ‖x‖ from
    tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n => norm_nonneg _) (fun n => opNorm_le_bound _ (hb₀ n) (this n)) hb_lim)
  intro n x
  -- Note that `f m x → g x`, hence `‖f n x - f m x‖ → ‖f n x - g x‖` as `m → ∞`
  have : Tendsto (fun m => ‖f n x - f m x‖) atTop (𝓝 ‖f n x - g x‖) :=
    (tendsto_const_nhds.sub <| tendsto_pi_nhds.1 hg _).norm
  -- Thus it suffices to verify `‖f n x - f m x‖ ≤ b n * ‖x‖` for `m ≥ n`.
  refine le_of_tendsto this (eventually_atTop.2 ⟨n, fun m hm => ?_⟩)
  -- This inequality follows from `‖f n - f m‖ ≤ b n`.
  exact (f n - f m).le_of_opNorm_le (hfb _ _ _ le_rfl hm) _

/--
theorem `isCompact_closure_image_coe_of_bounded` / 定理 `isCompact_closure_image_coe_of_bounded`

English:
theorem isCompact_closure_image_coe_of_bounded
  statement: [ProperSpace F] {s : Set (E' ->SL[σ₁₂] F)}
  proof: have : forall x, IsCompact (closure (apply' F σ₁₂ x '' s)) := fun x =>
    ((apply' F σ₁₂ x).lipschitz.isBounded_image hb).isCompact_closure
  (isCompact_pi_infinite this).closure_of_subset
    (image_subset_iff.2 fun _ hg _ => subset_closure <| mem_image_of_mem _ hg)

中文:
定理 isCompact_closure_image_coe_of_bounded
  结论: [命题erSpace F] {s : Set (E' ->SL[σ₁₂] F)}
  证明: have : forall x, IsCompact (closure (apply' F σ₁₂ x '' s)) := fun x =>
    ((apply' F σ₁₂ x).lipschitz.isBounded_image hb).isCompact_closure
  (isCompact_pi_infinite this).closure_of_subset
    (image_subset_iff.2 fun _ hg _ => subset_closure <| mem_image_of_mem _ hg)

Depends on / 依赖: IsCompact, closure, closure_of_subset, image_subset_iff, isBounded_image, isCompact_closure, isCompact_pi_infinite, lipschitz, lipschitz.isBounded_image, mem_image_of_mem, subset_closure
-/
theorem isCompact_closure_image_coe_of_bounded [ProperSpace F] {s : Set (E' ->SL[σ₁₂] F)}
    (hb : IsBounded s) : IsCompact (closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s)) :=
  have : forall x, IsCompact (closure (apply' F σ₁₂ x '' s)) := fun x =>
    ((apply' F σ₁₂ x).lipschitz.isBounded_image hb).isCompact_closure
  (isCompact_pi_infinite this).closure_of_subset
    (image_subset_iff.2 fun _ hg _ => subset_closure <| mem_image_of_mem _ hg)

/--
theorem `isCompact_image_coe_of_bounded_of_closed_image` / 定理 `isCompact_image_coe_of_bounded_of_closed_image`

English:
theorem isCompact_image_coe_of_bounded_of_closed_image
  statement: [ProperSpace F] {s : Set (E' ->SL[σ₁₂] F)}
  proof: hc.closure_eq ▸ isCompact_closure_image_coe_of_bounded hb

中文:
定理 isCompact_image_coe_of_bounded_of_closed_image
  结论: [命题erSpace F] {s : Set (E' ->SL[σ₁₂] F)}
  证明: hc.closure_eq ▸ isCompact_closure_image_coe_of_bounded hb

Depends on / 依赖: closure_eq, hc.closure_eq, isCompact_closure_image_coe_of_bounded
-/
theorem isCompact_image_coe_of_bounded_of_closed_image [ProperSpace F] {s : Set (E' ->SL[σ₁₂] F)}
    (hb : IsBounded s) (hc : IsClosed (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s)) :
    IsCompact (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s) :=
  hc.closure_eq ▸ isCompact_closure_image_coe_of_bounded hb

/--
theorem `isClosed_image_coe_of_bounded_of_weak_closed` / 定理 `isClosed_image_coe_of_bounded_of_weak_closed`

English:
theorem isClosed_image_coe_of_bounded_of_weak_closed
  statement: {s : Set (E' ->SL[σ₁₂] F)} (hb : IsBounded s)
  proof: isClosed_of_closure_subset fun f hf =>
    ⟨ofMemClosureImageCoeBounded f hb hf, hc (ofMemClosureImageCoeBounded f hb hf) hf, rfl⟩

中文:
定理 isClosed_image_coe_of_bounded_of_weak_closed
  结论: {s : Set (E' ->SL[σ₁₂] F)} (hb : IsBounded s)
  证明: isClosed_of_closure_subset fun f hf =>
    ⟨ofMemClosureImageCoeBounded f hb hf, hc (ofMemClosureImageCoeBounded f hb hf) hf, rfl⟩

Depends on / 依赖: isClosed_of_closure_subset, ofMemClosureImageCoeBounded
-/
theorem isClosed_image_coe_of_bounded_of_weak_closed {s : Set (E' ->SL[σ₁₂] F)} (hb : IsBounded s)
    (hc : forall f : E' ->SL[σ₁₂] F,
      (⇑f : E' -> F) in closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s) -> f in s) :
    IsClosed (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s) :=
  isClosed_of_closure_subset fun f hf =>
    ⟨ofMemClosureImageCoeBounded f hb hf, hc (ofMemClosureImageCoeBounded f hb hf) hf, rfl⟩

/--
theorem `isCompact_image_coe_of_bounded_of_weak_closed` / 定理 `isCompact_image_coe_of_bounded_of_weak_closed`

English:
theorem isCompact_image_coe_of_bounded_of_weak_closed
  statement: [ProperSpace F] {s : Set (E' ->SL[σ₁₂] F)}
  proof: isCompact_image_coe_of_bounded_of_closed_image hb
    isClosed_image_coe_of_bounded_of_weak_closed hb hc

中文:
定理 isCompact_image_coe_of_bounded_of_weak_closed
  结论: [命题erSpace F] {s : Set (E' ->SL[σ₁₂] F)}
  证明: isCompact_image_coe_of_bounded_of_closed_image hb
    isClosed_image_coe_of_bounded_of_weak_closed hb hc

Depends on / 依赖: isClosed_image_coe_of_bounded_of_weak_closed, isCompact_image_coe_of_bounded_of_closed_image
-/
theorem isCompact_image_coe_of_bounded_of_weak_closed [ProperSpace F] {s : Set (E' ->SL[σ₁₂] F)}
    (hb : IsBounded s) (hc : forall f : E' ->SL[σ₁₂] F,
      (⇑f : E' -> F) in closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s) -> f in s) :
    IsCompact (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' s) :=
isCompact_image_coe_of_bounded_of_closed_image hb
    isClosed_image_coe_of_bounded_of_weak_closed hb hc

/--
theorem `is_weak_closed_closedBall` / 定理 `is_weak_closed_closedBall`

English:
theorem is_weak_closed_closedBall
  given: (f₀ : E' ->SL[σ₁₂] F) (r : Real) ⦃f
  statement: E' ->SL[σ₁₂] F⦄
  proof: by
  have hr : 0 <= r := nonempty_closedBall.1 (closure_nonempty_iff.1 ⟨_, hf⟩).of_image
  refine mem_closedBall_iff_norm.2 (opNorm_le_bound _ hr fun x => ?_)
  have : IsClosed { g : E' -> F | ‖g x - f₀ x‖ <= r * ‖x‖ } :=
    isClosed_Iic.preimage ((@continuous_apply E' (fun _ => F) _ x).sub continu

中文:
定理 is_weak_closed_closedBall
  条件: (f₀ : E' ->SL[σ₁₂] F) (r : 实数) ⦃f
  结论: E' ->SL[σ₁₂] F⦄
  证明: by
  have hr : 0 <= r := nonempty_closedBall.1 (closure_nonempty_iff.1 ⟨_, hf⟩).of_image
  refine mem_closedBall_iff_norm.2 (opNorm_le_bound _ hr fun x => ?_)
  have : IsClosed { g : E' -> F | ‖g x - f₀ x‖ <= r * ‖x‖ } :=
    isClosed_Iic.preimage ((@continuous_apply E' (fun _ => F) _ x).sub continu

Depends on / 依赖: IsClosed, closure_nonempty_iff, closure_subset_iff, continuous_apply, continuous_const, image_subset_iff, isClosed_Iic, isClosed_Iic.preimage, le_of_opNorm_le, mem_closedBall_iff_norm, nonempty_closedBall, of_image, opNorm_le_bound, preimage, this.closure_subset_iff
-/
theorem is_weak_closed_closedBall (f₀ : E' ->SL[σ₁₂] F) (r : Real) ⦃f : E' ->SL[σ₁₂] F⦄
    (hf : ⇑f in closure (((↑) : (E' ->SL[σ₁₂] F) -> E' -> F) '' closedBall f₀ r)) :
    f in closedBall f₀ r := by
  have hr : 0 <= r := nonempty_closedBall.1 (closure_nonempty_iff.1 ⟨_, hf⟩).of_image
  refine mem_closedBall_iff_norm.2 (opNorm_le_bound _ hr fun x => ?_)
  have : IsClosed { g : E' -> F | ‖g x - f₀ x‖ <= r * ‖x‖ } :=
    isClosed_Iic.preimage ((@continuous_apply E' (fun _ => F) _ x).sub continuous_const).norm
  refine this.closure_subset_iff.2 (image_subset_iff.2 fun g hg => ?_) hf
  exact (g - f₀).le_of_opNorm_le (mem_closedBall_iff_norm.1 hg) _

/--
theorem `isClosed_image_coe_closedBall` / 定理 `isClosed_image_coe_closedBall`

English:
theorem isClosed_image_coe_closedBall
  given: (f₀ : E ->SL[σ₁₂] F) (r : Real)
  proof: isClosed_image_coe_of_bounded_of_weak_closed isBounded_closedBall (is_weak_closed_closedBall f₀ r)

中文:
定理 isClosed_image_coe_closedBall
  条件: (f₀ : E ->SL[σ₁₂] F) (r : 实数)
  证明: isClosed_image_coe_of_bounded_of_weak_closed isBounded_closedBall (is_weak_closed_closedBall f₀ r)

Depends on / 依赖: isBounded_closedBall, isClosed_image_coe_of_bounded_of_weak_closed, is_weak_closed_closedBall
-/
theorem isClosed_image_coe_closedBall (f₀ : E ->SL[σ₁₂] F) (r : Real) :
    IsClosed (((↑) : (E ->SL[σ₁₂] F) -> E -> F) '' closedBall f₀ r) :=
  isClosed_image_coe_of_bounded_of_weak_closed isBounded_closedBall (is_weak_closed_closedBall f₀ r)

/--
theorem `isCompact_image_coe_closedBall` / 定理 `isCompact_image_coe_closedBall`

English:
theorem isCompact_image_coe_closedBall
  given: [ProperSpace F] (f₀ : E ->SL[σ₁₂] F) (r : Real)
  proof: isCompact_image_coe_of_bounded_of_weak_closed isBounded_closedBall
    is_weak_closed_closedBall f₀ r

中文:
定理 isCompact_image_coe_closedBall
  条件: [命题erSpace F] (f₀ : E ->SL[σ₁₂] F) (r : 实数)
  证明: isCompact_image_coe_of_bounded_of_weak_closed isBounded_closedBall
    is_weak_closed_closedBall f₀ r

Depends on / 依赖: isBounded_closedBall, isCompact_image_coe_of_bounded_of_weak_closed, is_weak_closed_closedBall
-/
theorem isCompact_image_coe_closedBall [ProperSpace F] (f₀ : E ->SL[σ₁₂] F) (r : Real) :
    IsCompact (((↑) : (E ->SL[σ₁₂] F) -> E -> F) '' closedBall f₀ r) :=
isCompact_image_coe_of_bounded_of_weak_closed isBounded_closedBall
    is_weak_closed_closedBall f₀ r

end Completeness

end ContinuousLinearMap
