/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Birkhoff average in a normed space

In this file we prove some lemmas about the Birkhoff average (`birkhoffAverage`)
of a function which takes values in a normed space over `ℝ` or `ℂ`.

At the time of writing, all lemmas in this file
are motivated by the proof of the von Neumann Mean Ergodic Theorem,
see `LinearIsometry.tendsto_birkhoffAverage_orthogonalProjection`.
-/

public section

open Function Set Filter
open scoped Topology ENNReal Uniformity

section

variable {α E : Type*}

/--
theorem `Function.IsFixedPt.tendsto_birkhoffAverage` / 定理 `Function.IsFixedPt.tendsto_birkhoffAverage`

English:
theorem Function.IsFixedPt.tendsto_birkhoffAverage
  proof: tendsto_const_nhds.congr' (eventually_ne_atTop 0).mono fun _n hn =>
    (h.birkhoffAverage_eq R g (Nat.cast_ne_zero.mpr hn)).symm

中文:
定理 Function.IsFixedPt.tendsto_birkhoffAverage
  证明: tendsto_const_nhds.congr' (eventually_ne_atTop 0).mono fun _n hn =>
    (h.birkhoffAverage_eq R g (Nat.cast_ne_zero.mpr hn)).symm

Depends on / 依赖: CompTriple, CompTriple.comp_inv, MulActionHom, MulActionHom.id, Nat.cast_ne_zero.mpr, birkhoffAverage_eq, cast_ne_zero, comp_inv, eventually_ne_atTop, h.birkhoffAverage_eq, tendsto_const_nhds, tendsto_const_nhds.congr
-/
theorem Function.IsFixedPt.tendsto_birkhoffAverage
    (R : Type*) [DivisionSemiring R] [CharZero R]
    [AddCommMonoid E] [TopologicalSpace E] [Module R E]
    {f : α -> α} {x : α} (h : f.IsFixedPt x) (g : α -> E) :
    Tendsto (birkhoffAverage R f g · x) atTop (𝓝 (g x)) :=
tendsto_const_nhds.congr' (eventually_ne_atTop 0).mono fun _n hn =>
    (h.birkhoffAverage_eq R g (Nat.cast_ne_zero.mpr hn)).symm

variable [NormedAddCommGroup E]

/--
theorem `dist_birkhoffSum_apply_birkhoffSum` / 定理 `dist_birkhoffSum_apply_birkhoffSum`

English:
theorem dist_birkhoffSum_apply_birkhoffSum
  given: (f : α -> α) (g : α -> E) (n : Nat) (x : α)
  proof: by
  simp only [dist_eq_norm, birkhoffSum_apply_sub_birkhoffSum]

中文:
定理 dist_birkhoffSum_apply_birkhoffSum
  条件: (f : α -> α) (g : α -> E) (n : 自然数) (x : α)
  证明: by
  simp only [dist_eq_norm, birkhoffSum_apply_sub_birkhoffSum]

Depends on / 依赖: birkhoffSum_apply_sub_birkhoffSum, dist_eq_norm
-/
theorem dist_birkhoffSum_apply_birkhoffSum (f : α -> α) (g : α -> E) (n : Nat) (x : α) :
    dist (birkhoffSum f g n (f x)) (birkhoffSum f g n x) = dist (g (f^[n] x)) (g x) := by
  simp only [dist_eq_norm, birkhoffSum_apply_sub_birkhoffSum]

/--
theorem `dist_birkhoffSum_birkhoffSum_le` / 定理 `dist_birkhoffSum_birkhoffSum_le`

English:
theorem dist_birkhoffSum_birkhoffSum_le
  given: (f : α -> α) (g : α -> E) (n : Nat) (x y : α)
  proof: dist_sum_sum_le _ _ _

中文:
定理 dist_birkhoffSum_birkhoffSum_le
  条件: (f : α -> α) (g : α -> E) (n : 自然数) (x y : α)
  证明: dist_sum_sum_le _ _ _

Depends on / 依赖: dist_sum_sum_le
-/
theorem dist_birkhoffSum_birkhoffSum_le (f : α -> α) (g : α -> E) (n : Nat) (x y : α) :
    dist (birkhoffSum f g n x) (birkhoffSum f g n y) <=
      ∑ k in Finset.range n, dist (g (f^[k] x)) (g (f^[k] y)) :=
  dist_sum_sum_le _ _ _

variable (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 E]

/--
theorem `dist_birkhoffAverage_birkhoffAverage` / 定理 `dist_birkhoffAverage_birkhoffAverage`

English:
theorem dist_birkhoffAverage_birkhoffAverage
  given: (f : α -> α) (g : α -> E) (n : Nat) (x y : α)
  proof: by
  simp [birkhoffAverage, dist_smul₀, div_eq_inv_mul]

中文:
定理 dist_birkhoffAverage_birkhoffAverage
  条件: (f : α -> α) (g : α -> E) (n : 自然数) (x y : α)
  证明: by
  simp [birkhoffAverage, dist_smul₀, div_eq_inv_mul]

Depends on / 依赖: birkhoffAverage, div_eq_inv_mul
-/
theorem dist_birkhoffAverage_birkhoffAverage (f : α -> α) (g : α -> E) (n : Nat) (x y : α) :
    dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y) =
      dist (birkhoffSum f g n x) (birkhoffSum f g n y) / n := by
  simp [birkhoffAverage, dist_smul₀, div_eq_inv_mul]

/--
theorem `dist_birkhoffAverage_birkhoffAverage_le` / 定理 `dist_birkhoffAverage_birkhoffAverage_le`

English:
theorem dist_birkhoffAverage_birkhoffAverage_le
  given: (f : α -> α) (g : α -> E) (n : Nat) (x y : α)
  proof: (dist_birkhoffAverage_birkhoffAverage _ _ _ _ _ _).trans_le by
    gcongr; apply dist_birkhoffSum_birkhoffSum_le

中文:
定理 dist_birkhoffAverage_birkhoffAverage_le
  条件: (f : α -> α) (g : α -> E) (n : 自然数) (x y : α)
  证明: (dist_birkhoffAverage_birkhoffAverage _ _ _ _ _ _).trans_le by
    gcongr; apply dist_birkhoffSum_birkhoffSum_le

Depends on / 依赖: dist_birkhoffAverage_birkhoffAverage, dist_birkhoffSum_birkhoffSum_le, trans_le
-/
theorem dist_birkhoffAverage_birkhoffAverage_le (f : α -> α) (g : α -> E) (n : Nat) (x y : α) :
    dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y) <=
      (∑ k in Finset.range n, dist (g (f^[k] x)) (g (f^[k] y))) / n :=
(dist_birkhoffAverage_birkhoffAverage _ _ _ _ _ _).trans_le by
    gcongr; apply dist_birkhoffSum_birkhoffSum_le

/--
theorem `dist_birkhoffAverage_apply_birkhoffAverage` / 定理 `dist_birkhoffAverage_apply_birkhoffAverage`

English:
theorem dist_birkhoffAverage_apply_birkhoffAverage
  given: (f : α -> α) (g : α -> E) (n : Nat) (x : α)
  proof: by
  simp [dist_birkhoffAverage_birkhoffAverage, dist_birkhoffSum_apply_birkhoffSum]

中文:
定理 dist_birkhoffAverage_apply_birkhoffAverage
  条件: (f : α -> α) (g : α -> E) (n : 自然数) (x : α)
  证明: by
  simp [dist_birkhoffAverage_birkhoffAverage, dist_birkhoffSum_apply_birkhoffSum]

Depends on / 依赖: dist_birkhoffAverage_birkhoffAverage, dist_birkhoffSum_apply_birkhoffSum
-/
theorem dist_birkhoffAverage_apply_birkhoffAverage (f : α -> α) (g : α -> E) (n : Nat) (x : α) :
    dist (birkhoffAverage 𝕜 f g n (f x)) (birkhoffAverage 𝕜 f g n x) =
      dist (g (f^[n] x)) (g x) / n := by
  simp [dist_birkhoffAverage_birkhoffAverage, dist_birkhoffSum_apply_birkhoffSum]

/--
theorem `tendsto_birkhoffAverage_apply_sub_birkhoffAverage` / 定理 `tendsto_birkhoffAverage_apply_sub_birkhoffAverage`

English:
theorem tendsto_birkhoffAverage_apply_sub_birkhoffAverage
  statement: {f : α -> α} {g : α -> E} {x : α}
  proof: by
  rcases Metric.isBounded_range_iff.1 h with ⟨C, hC⟩
  have : Tendsto (fun n : Nat => C / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm (fun n => ?_) this
  rw [← dist_eq_norm]; rw [dist_birkhoffAverage_apply_birkhoffAverage]
  gcongr
  

中文:
定理 tendsto_birkhoffAverage_apply_sub_birkhoffAverage
  结论: {f : α -> α} {g : α -> E} {x : α}
  证明: by
  rcases Metric.isBounded_range_iff.1 h with ⟨C, hC⟩
  have : Tendsto (fun n : Nat => C / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm (fun n => ?_) this
  rw [← dist_eq_norm]; rw [dist_birkhoffAverage_apply_birkhoffAverage]
  gcongr
  

Depends on / 依赖: Metric, Metric.isBounded_range_iff, Tendsto, dist_birkhoffAverage_apply_birkhoffAverage, dist_eq_norm, div_atTop, isBounded_range_iff, squeeze_zero_norm, tendsto_const_nhds, tendsto_const_nhds.div_atTop, tendsto_natCast_atTop_atTop
-/
theorem tendsto_birkhoffAverage_apply_sub_birkhoffAverage {f : α -> α} {g : α -> E} {x : α}
    (h : Bornology.IsBounded (range (g <| f^[·] x))) :
    Tendsto (fun n => birkhoffAverage 𝕜 f g n (f x) - birkhoffAverage 𝕜 f g n x) atTop (𝓝 0) := by
  rcases Metric.isBounded_range_iff.1 h with ⟨C, hC⟩
  have : Tendsto (fun n : Nat => C / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm (fun n => ?_) this
  rw [← dist_eq_norm]; rw [dist_birkhoffAverage_apply_birkhoffAverage]
  gcongr
  exact hC n 0

/--
theorem `tendsto_birkhoffAverage_apply_sub_birkhoffAverage'` / 定理 `tendsto_birkhoffAverage_apply_sub_birkhoffAverage'`

English:
theorem tendsto_birkhoffAverage_apply_sub_birkhoffAverage'
  statement: {g : α -> E}
  proof: tendsto_birkhoffAverage_apply_sub_birkhoffAverage _ h.subset range_comp_subset_range _ _

中文:
定理 tendsto_birkhoffAverage_apply_sub_birkhoffAverage'
  结论: {g : α -> E}
  证明: tendsto_birkhoffAverage_apply_sub_birkhoffAverage _ h.subset range_comp_subset_range _ _

Depends on / 依赖: h.subset, range_comp_subset_range, subset, tendsto_birkhoffAverage_apply_sub_birkhoffAverage
-/
theorem tendsto_birkhoffAverage_apply_sub_birkhoffAverage' {g : α -> E}
    (h : Bornology.IsBounded (range g)) (f : α -> α) (x : α) :
    Tendsto (fun n => birkhoffAverage 𝕜 f g n (f x) - birkhoffAverage 𝕜 f g n x) atTop (𝓝 0) :=
tendsto_birkhoffAverage_apply_sub_birkhoffAverage _ h.subset range_comp_subset_range _ _

end

variable (𝕜 : Type*) {X E : Type*}
  [PseudoEMetricSpace X] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : X -> X} {g : X -> E} {l : X -> E}

/--
theorem `uniformEquicontinuous_birkhoffAverage` / 定理 `uniformEquicontinuous_birkhoffAverage`

English:
theorem uniformEquicontinuous_birkhoffAverage
  given: (hf : LipschitzWith 1 f) (hg : UniformContinuous g)
  proof: by
  refine Metric.uniformity_basis_dist_le.uniformEquicontinuous_iff_right.2 fun ε hε => ?_
  rcases (uniformity_basis_edist_le.uniformContinuous_iff Metric.uniformity_basis_dist_le).1 hg ε hε
    with ⟨δ, hδ₀, hδε⟩
  refine mem_uniformity_edist.2 ⟨δ, hδ₀, fun {x y} h n => ?_⟩
  calc
    dist (birk

中文:
定理 uniformEquicontinuous_birkhoffAverage
  条件: (hf : LipschitzWith 1 f) (hg : UniformContinuous g)
  证明: by
  refine Metric.uniformity_basis_dist_le.uniformEquicontinuous_iff_right.2 fun ε hε => ?_
  rcases (uniformity_basis_edist_le.uniformContinuous_iff Metric.uniformity_basis_dist_le).1 hg ε hε
    with ⟨δ, hδ₀, hδε⟩
  refine mem_uniformity_edist.2 ⟨δ, hδ₀, fun {x y} h n => ?_⟩
  calc
    dist (birk

Depends on / 依赖: Finset, Finset.range, Metric, Metric.uniformity_basis_dist_le, Metric.uniformity_basis_dist_le.uniformEquicontinuous_iff_right, birkhoffAverage, dist_birkhoffAverage_birkhoffAverage_le, mem_uniformity_edist, uniformContinuous_iff, uniformEquicontinuous_iff_right, uniformity_basis_dist_le, uniformity_basis_edist_le, uniformity_basis_edist_le.uniformContinuous_iff
-/
theorem uniformEquicontinuous_birkhoffAverage (hf : LipschitzWith 1 f) (hg : UniformContinuous g) :
    UniformEquicontinuous (birkhoffAverage 𝕜 f g) := by
  refine Metric.uniformity_basis_dist_le.uniformEquicontinuous_iff_right.2 fun ε hε => ?_
  rcases (uniformity_basis_edist_le.uniformContinuous_iff Metric.uniformity_basis_dist_le).1 hg ε hε
    with ⟨δ, hδ₀, hδε⟩
  refine mem_uniformity_edist.2 ⟨δ, hδ₀, fun {x y} h n => ?_⟩
  calc
    dist (birkhoffAverage 𝕜 f g n x) (birkhoffAverage 𝕜 f g n y)
      <= (∑ k in Finset.range n, dist (g (f^[k] x)) (g (f^[k] y))) / n :=
      dist_birkhoffAverage_birkhoffAverage_le ..
    _ <= (∑ _k in Finset.range n, ε) / n := by
      gcongr
      refine hδε _ _ ?_
      simpa using (hf.iterate _).edist_le_mul_of_le h.le
    _ = n * ε / n := by simp
    _ <= ε := by
      rcases eq_or_ne n 0 with hn | hn <;> simp [hn, hε.le, mul_div_cancel_left₀]

/--
theorem `isClosed_setOfPred_tendsto_birkhoffAverage` / 定理 `isClosed_setOfPred_tendsto_birkhoffAverage`

English:
theorem isClosed_setOfPred_tendsto_birkhoffAverage
  proof: (uniformEquicontinuous_birkhoffAverage 𝕜 hf hg).equicontinuous.isClosed_setOfPred_tendsto hl

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_tendsto_birkhoffAverage := isClosed_setOfPred_tendsto_birkhoffAverage

中文:
定理 isClosed_setOfPred_tendsto_birkhoffAverage
  证明: (uniformEquicontinuous_birkhoffAverage 𝕜 hf hg).equicontinuous.isClosed_setOfPred_tendsto hl

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_tendsto_birkhoffAverage := isClosed_setOfPred_tendsto_birkhoffAverage

Depends on / 依赖: equicontinuous, equicontinuous.isClosed_setOfPred_tendsto, isClosed_setOfPred_tendsto, uniformEquicontinuous_birkhoffAverage
-/
theorem isClosed_setOfPred_tendsto_birkhoffAverage
    (hf : LipschitzWith 1 f) (hg : UniformContinuous g) (hl : Continuous l) :
    IsClosed {x | Tendsto (birkhoffAverage 𝕜 f g · x) atTop (𝓝 (l x))} :=
  (uniformEquicontinuous_birkhoffAverage 𝕜 hf hg).equicontinuous.isClosed_setOfPred_tendsto hl

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_tendsto_birkhoffAverage := isClosed_setOfPred_tendsto_birkhoffAverage
