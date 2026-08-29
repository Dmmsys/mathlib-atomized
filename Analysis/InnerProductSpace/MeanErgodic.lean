/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Dynamics.BirkhoffSum.NormedSpace

/-!
# Von Neumann Mean Ergodic Theorem in a Hilbert Space

In this file we prove the von Neumann Mean Ergodic Theorem for an operator in a Hilbert space.
It says that for a contracting linear self-map `f : E →ₗ[𝕜] E` of a Hilbert space,
the Birkhoff averages
```
birkhoffAverage 𝕜 f id N x = (N : 𝕜)⁻¹ • ∑ n ∈ Finset.range N, f^[n] x
```
converge to the orthogonal projection of `x` to the subspace of fixed points of `f`,
see `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`.
-/

public section

open Filter Finset Function Bornology
open scoped Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]

/--
theorem `LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure` / 定理 `LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure`

English:
theorem LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure
  statement: [NormedSpace 𝕜 E]
  proof: by
  /- Any point can be represented as a sum of `y ∈ LinearMap.ker g` and a fixed point `z`. -/
  obtain ⟨y, hy, z, hz, rfl⟩ : exists y, g y = 0 ∧ exists z, IsFixedPt f z ∧ x = y + z :=
    ⟨x - g x, by simp [hg_proj], g x, (g x).2, by simp⟩
  /- For a fixed point, the theorem is trivial,
  so it suffices to prove it for `y ∈ LinearMap.ker g`. -/
  suffices Tendsto (birkhoffAverage 𝕜 f _root_.id · y) atTop (𝓝 0) by
    have hgz : g z = z := congr_arg Subtype.val (hg_proj ⟨z, hz⟩)
    simpa [hy, hgz, birkhoffAverage, birkhoffSum, Finset.sum_add_distrib, smul_add]
      using this.add (hz.tendsto_birkhoffAverage 𝕜 _root_.id)
  /- By continuity, it suffices to prove the theorem on a dense subset of `LinearMap.ker g`.
  By assumption, `LinearMap.range (f - 1)` is dense in the kernel of `g`,
  so it suffices to prove the theorem for `y = f x - x`. -/
  have : IsClosed {x | Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 0)} :=
    isClosed_setOfPred_tendsto_birkhoffAverage 𝕜 hf uniformContinuous_id continuous_const
  refine closure_minimal (Set.forall_mem_range.2 fun x => ?_) this (hg_ker hy)
  /- Finally, for `y = f x - x` the average is equal to the difference between averages
  along the orbits of `f x` and `x`, and most of the terms cancel. -/
  have : IsBounded (Set.range (_root_.id <| f^[·] x)) :=
    isBounded_iff_forall_norm_le.2 ⟨‖x‖, Set.forall_mem_range.2 fun n => by
      have H : f^[n] 0 = 0 := iterate_map_zero (f : E ->+ E) n
      simpa [H] using (hf.iterate n).dist_le_mul x 0⟩
  have H : forall n x y, f^[n] (x - y) = f^[n] x - f^[n] y := iterate_map_sub (f : E ->+ E)
  simpa [birkhoffAverage, birkhoffSum, Finset.sum_sub_distrib, smul_sub, H]
    using tendsto_birkhoffAverage_apply_sub_birkhoffAverage 𝕜 this

中文:
定理 线性映射.tendsto_birkhoffAverage_of_ker_subset_closure
  结论: [赋范空间 𝕜 E]
  证明: by
  /- Any point can be represented as a sum of `y ∈ LinearMap.ker g` and a fixed point `z`. -/
  obtain ⟨y, hy, z, hz, rfl⟩ : exists y, g y = 0 ∧ exists z, IsFixedPt f z ∧ x = y + z :=
    ⟨x - g x, by simp [hg_proj], g x, (g x).2, by simp⟩
  /- For a fixed point, the theorem is trivial,
  so it suffices to prove it for `y ∈ LinearMap.ker g`. -/
  suffices Tendsto (birkhoffAverage 𝕜 f _root_.id · y) atTop (𝓝 0) by
    have hgz : g z = z := congr_arg Subtype.val (hg_proj ⟨z, hz⟩)
    simpa [hy, hgz, birkhoffAverage, birkhoffSum, Finset.sum_add_distrib, smul_add]
      using this.add (hz.tendsto_birkhoffAverage 𝕜 _root_.id)
  /- By continuity, it suffices to prove the theorem on a dense subset of `LinearMap.ker g`.
  By assumption, `LinearMap.range (f - 1)` is dense in the kernel of `g`,
  so it suffices to prove the theorem for `y = f x - x`. -/
  have : IsClosed {x | Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 0)} :=
    isClosed_setOfPred_tendsto_birkhoffAverage 𝕜 hf uniformContinuous_id continuous_const
  refine closure_minimal (Set.forall_mem_range.2 fun x => ?_) this (hg_ker hy)
  /- Finally, for `y = f x - x` the average is equal to the difference between averages
  along the orbits of `f x` and `x`, and most of the terms cancel. -/
  have : IsBounded (Set.range (_root_.id <| f^[·] x)) :=
    isBounded_iff_forall_norm_le.2 ⟨‖x‖, Set.forall_mem_range.2 fun n => by
      have H : f^[n] 0 = 0 := iterate_map_zero (f : E ->+ E) n
      simpa [H] using (hf.iterate n).dist_le_mul x 0⟩
  have H : forall n x y, f^[n] (x - y) = f^[n] x - f^[n] y := iterate_map_sub (f : E ->+ E)
  simpa [birkhoffAverage, birkhoffSum, Finset.sum_sub_distrib, smul_sub, H]
    using tendsto_birkhoffAverage_apply_sub_birkhoffAverage 𝕜 this
-/
theorem LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure [NormedSpace 𝕜 E]
    (f : E ->ₗ[𝕜] E) (hf : LipschitzWith 1 f) (g : E ->L[𝕜] LinearMap.eqLocus f 1)
    (hg_proj : forall x : LinearMap.eqLocus f 1, g x = x)
    (hg_ker : (g.ker : Set E) subseteq closure (LinearMap.range (f - 1))) (x : E) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 (g x)) := by
  /- Any point can be represented as a sum of `y ∈ LinearMap.ker g` and a fixed point `z`. -/
  obtain ⟨y, hy, z, hz, rfl⟩ : exists y, g y = 0 ∧ exists z, IsFixedPt f z ∧ x = y + z :=
    ⟨x - g x, by simp [hg_proj], g x, (g x).2, by simp⟩
  /- For a fixed point, the theorem is trivial,
  so it suffices to prove it for `y ∈ LinearMap.ker g`. -/
  suffices Tendsto (birkhoffAverage 𝕜 f _root_.id · y) atTop (𝓝 0) by
    have hgz : g z = z := congr_arg Subtype.val (hg_proj ⟨z, hz⟩)
    simpa [hy, hgz, birkhoffAverage, birkhoffSum, Finset.sum_add_distrib, smul_add]
      using this.add (hz.tendsto_birkhoffAverage 𝕜 _root_.id)
  /- By continuity, it suffices to prove the theorem on a dense subset of `LinearMap.ker g`.
  By assumption, `LinearMap.range (f - 1)` is dense in the kernel of `g`,
  so it suffices to prove the theorem for `y = f x - x`. -/
  have : IsClosed {x | Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop (𝓝 0)} :=
    isClosed_setOfPred_tendsto_birkhoffAverage 𝕜 hf uniformContinuous_id continuous_const
  refine closure_minimal (Set.forall_mem_range.2 fun x => ?_) this (hg_ker hy)
  /- Finally, for `y = f x - x` the average is equal to the difference between averages
  along the orbits of `f x` and `x`, and most of the terms cancel. -/
  have : IsBounded (Set.range (_root_.id <| f^[·] x)) :=
    isBounded_iff_forall_norm_le.2 ⟨‖x‖, Set.forall_mem_range.2 fun n => by
      have H : f^[n] 0 = 0 := iterate_map_zero (f : E ->+ E) n
      simpa [H] using (hf.iterate n).dist_le_mul x 0⟩
  have H : forall n x y, f^[n] (x - y) = f^[n] x - f^[n] y := iterate_map_sub (f : E ->+ E)
  simpa [birkhoffAverage, birkhoffSum, Finset.sum_sub_distrib, smul_sub, H]
    using tendsto_birkhoffAverage_apply_sub_birkhoffAverage 𝕜 this

variable [InnerProductSpace 𝕜 E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` / 定理 `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`

English:
theorem ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
  statement: (f : E ->L[𝕜] E)
  proof: by
  /- Due to the previous theorem, it suffices to verify
  that the range of `f - 1` is dense in the orthogonal complement
  to the submodule of fixed points of `f`. -/
  apply (f : E ->ₗ[𝕜] E).tendsto_birkhoffAverage_of_ker_subset_closure (f.lipschitz.weaken hf)
  · exact (f.eqLocus (1 : E ->L[𝕜] E)).orthogonalProjectionOnto_mem_subspace_eq_self
  · clear x
    /- In other words, we need to verify that any vector that is orthogonal to the range of `f - 1`
    is a fixed point of `f`. -/
    rw [Submodule.ker_orthogonalProjectionOnto]; rw [← Submodule.topologicalClosure_coe]; rw [SetLike.coe_subset_coe]; rw [← Submodule.orthogonal_orthogonal_eq_closure]
    /- To verify this, we verify `‖f x‖ ≤ ‖x‖` (because `‖f‖ ≤ 1`) and `⟪f x, x⟫ = ‖x‖²`. -/
    refine Submodule.orthogonal_le fun x hx => eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜) ?_ ?_
    · simpa using f.le_of_opNorm_le hf x
    · have : forall y, ⟪f y, x⟫ = ⟪y, x⟫ := by
        simpa [Submodule.mem_orthogonal, inner_sub_left, sub_eq_zero] using hx
      simp [this]

中文:
定理 连续线性映射.tendsto_birkhoffAverage_orthogonalProjection
  结论: (f : E ->L[𝕜] E)
  证明: by
  /- Due to the previous theorem, it suffices to verify
  that the range of `f - 1` is dense in the orthogonal complement
  to the submodule of fixed points of `f`. -/
  apply (f : E ->ₗ[𝕜] E).tendsto_birkhoffAverage_of_ker_subset_closure (f.lipschitz.weaken hf)
  · exact (f.eqLocus (1 : E ->L[𝕜] E)).orthogonalProjectionOnto_mem_subspace_eq_self
  · clear x
    /- In other words, we need to verify that any vector that is orthogonal to the range of `f - 1`
    is a fixed point of `f`. -/
    rw [Submodule.ker_orthogonalProjectionOnto]; rw [← Submodule.topologicalClosure_coe]; rw [SetLike.coe_subset_coe]; rw [← Submodule.orthogonal_orthogonal_eq_closure]
    /- To verify this, we verify `‖f x‖ ≤ ‖x‖` (because `‖f‖ ≤ 1`) and `⟪f x, x⟫ = ‖x‖²`. -/
    refine Submodule.orthogonal_le fun x hx => eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜) ?_ ?_
    · simpa using f.le_of_opNorm_le hf x
    · have : forall y, ⟪f y, x⟫ = ⟪y, x⟫ := by
        simpa [Submodule.mem_orthogonal, inner_sub_left, sub_eq_zero] using hx
      simp [this]
-/
theorem ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection (f : E ->L[𝕜] E)
    (hf : ‖f‖ <= 1) (x : E) :
    Tendsto (birkhoffAverage 𝕜 f _root_.id · x) atTop
      (𝓝 <| (f.eqLocus (1 : E ->L[𝕜] E)).orthogonalProjectionOnto x) := by
  /- Due to the previous theorem, it suffices to verify
  that the range of `f - 1` is dense in the orthogonal complement
  to the submodule of fixed points of `f`. -/
  apply (f : E ->ₗ[𝕜] E).tendsto_birkhoffAverage_of_ker_subset_closure (f.lipschitz.weaken hf)
  · exact (f.eqLocus (1 : E ->L[𝕜] E)).orthogonalProjectionOnto_mem_subspace_eq_self
  · clear x
    /- In other words, we need to verify that any vector that is orthogonal to the range of `f - 1`
    is a fixed point of `f`. -/
    rw [Submodule.ker_orthogonalProjectionOnto]; rw [← Submodule.topologicalClosure_coe]; rw [SetLike.coe_subset_coe]; rw [← Submodule.orthogonal_orthogonal_eq_closure]
    /- To verify this, we verify `‖f x‖ ≤ ‖x‖` (because `‖f‖ ≤ 1`) and `⟪f x, x⟫ = ‖x‖²`. -/
    refine Submodule.orthogonal_le fun x hx => eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜) ?_ ?_
    · simpa using f.le_of_opNorm_le hf x
    · have : forall y, ⟪f y, x⟫ = ⟪y, x⟫ := by
        simpa [Submodule.mem_orthogonal, inner_sub_left, sub_eq_zero] using hx
      simp [this]
