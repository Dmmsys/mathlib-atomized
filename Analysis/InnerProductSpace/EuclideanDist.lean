/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Euclidean distance on a finite-dimensional space

When we define a smooth bump function on a normed space, it is useful to have a smooth distance on
the space. Since the default distance is not guaranteed to be smooth, we define `toEuclidean` to be
an equivalence between a finite-dimensional topological vector space and the standard Euclidean
space of the same dimension.
Then we define `Euclidean.dist x y = dist (toEuclidean x) (toEuclidean y)` and
provide some definitions (`Euclidean.ball`, `Euclidean.closedBall`) and simple lemmas about this
distance. This way we hide the usage of `toEuclidean` behind an API.
-/

@[expose] public section


open scoped Topology

open Set

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module Real E] [ContinuousSMul Real E] [FiniteDimensional Real E]

noncomputable section

open Module

/--
Definition of `toEuclidean` / `toEuclidean` 的定义

English:
definition toEuclidean
  signature: : E ≃L[Real] EuclideanSpace Real (Fin <| finrank Real E)
  body: ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

中文:
定义 toEuclidean
  签名: : E ≃L[实数] EuclideanSpace 实数 (有限集 <| finrank 实数 E)
  定义体: ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofFinrankEq, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin.symm, ofFinrankEq
-/
def toEuclidean : E ≃L[Real] EuclideanSpace Real (Fin <| finrank Real E) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

namespace Euclidean

/-- If `x` and `y` are two points in a finite-dimensional space over `ℝ`, then `Euclidean.dist x y`
is the distance between these points in the metric defined by some inner product space structure on
`E`. -/
nonrec def dist (x y : E) : Real :=
  dist (toEuclidean x) (toEuclidean y)

/--
Definition of `closedBall` / `closedBall` 的定义

English:
definition closedBall
  signature: (x : E) (r : Real)
  body: {y | dist y x <= r}

中文:
定义 closedBall
  签名: (x : E) (r : 实数)
  定义体: {y | dist y x <= r}

Depends on / 依赖: NormSMulClass, NormedSpace, NormedSpace.toNormSMulClass, toNormSMulClass
-/
def closedBall (x : E) (r : Real) : Set E :=
  {y | dist y x <= r}

/--
Definition of `ball` / `ball` 的定义

English:
definition ball
  signature: (x : E) (r : Real)
  body: {y | dist y x < r}

中文:
定义 ball
  签名: (x : E) (r : 实数)
  定义体: {y | dist y x < r}
-/
def ball (x : E) (r : Real) : Set E :=
  {y | dist y x < r}

/--
theorem `ball_eq_preimage` / 定理 `ball_eq_preimage`

English:
theorem ball_eq_preimage
  given: (x : E) (r : Real)
  proof: rfl

中文:
定理 ball_eq_preimage
  条件: (x : E) (r : 实数)
  证明: rfl
-/
theorem ball_eq_preimage (x : E) (r : Real) :
    ball x r = toEuclidean ⁻¹' Metric.ball (toEuclidean x) r :=
  rfl

/--
theorem `closedBall_eq_preimage` / 定理 `closedBall_eq_preimage`

English:
theorem closedBall_eq_preimage
  given: (x : E) (r : Real)
  proof: rfl

中文:
定理 closedBall_eq_preimage
  条件: (x : E) (r : 实数)
  证明: rfl
-/
theorem closedBall_eq_preimage (x : E) (r : Real) :
    closedBall x r = toEuclidean ⁻¹' Metric.closedBall (toEuclidean x) r :=
  rfl

/--
theorem `ball_subset_closedBall` / 定理 `ball_subset_closedBall`

English:
theorem ball_subset_closedBall
  given: {x : E} {r : Real}
  statement: ball x r subseteq closedBall x r
  proof: fun _ (hy : _ < r) =>
  le_of_lt hy

中文:
定理 ball_subset_closedBall
  条件: {x : E} {r : 实数}
  结论: ball x r subseteq closedBall x r
  证明: fun _ (hy : _ < r) =>
  le_of_lt hy
-/
theorem ball_subset_closedBall {x : E} {r : Real} : ball x r subseteq closedBall x r := fun _ (hy : _ < r) =>
  le_of_lt hy

/--
theorem `isOpen_ball` / 定理 `isOpen_ball`

English:
theorem isOpen_ball
  given: {x : E} {r : Real}
  statement: IsOpen (ball x r)
  proof: Metric.isOpen_ball.preimage toEuclidean.continuous

中文:
定理 isOpen_ball
  条件: {x : E} {r : 实数}
  结论: 是开集 (ball x r)
  证明: Metric.isOpen_ball.preimage toEuclidean.continuous
-/
@[simp] theorem isOpen_ball {x : E} {r : Real} : IsOpen (ball x r) :=
  Metric.isOpen_ball.preimage toEuclidean.continuous

/--
theorem `mem_ball_self` / 定理 `mem_ball_self`

English:
theorem mem_ball_self
  given: {x : E} {r : Real} (hr : 0 < r)
  statement: x in ball x r
  proof: Metric.mem_ball_self hr

中文:
定理 mem_ball_self
  条件: {x : E} {r : 实数} (hr : 0 < r)
  结论: x in ball x r
  证明: Metric.mem_ball_self hr

Depends on / 依赖: Metric, Metric.mem_ball_self, mem_ball_self
-/
theorem mem_ball_self {x : E} {r : Real} (hr : 0 < r) : x in ball x r :=
  Metric.mem_ball_self hr

/--
theorem `closedBall_eq_image` / 定理 `closedBall_eq_image`

English:
theorem closedBall_eq_image
  given: (x : E) (r : Real)
  proof: by
  rw [toEuclidean.image_symm_eq_preimage]; rw [closedBall_eq_preimage]

nonrec theorem isCompact_closedBall {x : E} {r : Real} : IsCompact (closedBall x r) := by
  rw [closedBall_eq_image]
  exact (isCompact_closedBall _ _).image toEuclidean.symm.continuous

中文:
定理 closedBall_eq_image
  条件: (x : E) (r : 实数)
  证明: by
  rw [toEuclidean.image_symm_eq_preimage]; rw [closedBall_eq_preimage]

nonrec theorem isCompact_closedBall {x : E} {r : Real} : IsCompact (closedBall x r) := by
  rw [closedBall_eq_image]
  exact (isCompact_closedBall _ _).image toEuclidean.symm.continuous

Depends on / 依赖: closedBall_eq_preimage, image_symm_eq_preimage, toEuclidean, toEuclidean.image_symm_eq_preimage
-/
theorem closedBall_eq_image (x : E) (r : Real) :
    closedBall x r = toEuclidean.symm '' Metric.closedBall (toEuclidean x) r := by
  rw [toEuclidean.image_symm_eq_preimage]; rw [closedBall_eq_preimage]

nonrec theorem isCompact_closedBall {x : E} {r : Real} : IsCompact (closedBall x r) := by
  rw [closedBall_eq_image]
  exact (isCompact_closedBall _ _).image toEuclidean.symm.continuous

/--
theorem `isClosed_closedBall` / 定理 `isClosed_closedBall`

English:
theorem isClosed_closedBall
  given: {x : E} {r : Real}
  statement: IsClosed (closedBall x r)
  proof: isCompact_closedBall.isClosed

nonrec theorem closure_ball (x : E) {r : Real} (h : r != 0) : closure (ball x r) = closedBall x r := by
  rw [ball_eq_preimage]; rw [← toEuclidean.preimage_closure]; rw [closure_ball (toEuclidean x) h]; rw [closedBall_eq_preimage]

nonrec theorem exists_pos_lt_subset_b

中文:
定理 isClosed_closedBall
  条件: {x : E} {r : 实数}
  结论: 是闭集 (closedBall x r)
  证明: isCompact_closedBall.isClosed

nonrec theorem closure_ball (x : E) {r : Real} (h : r != 0) : closure (ball x r) = closedBall x r := by
  rw [ball_eq_preimage]; rw [← toEuclidean.preimage_closure]; rw [closure_ball (toEuclidean x) h]; rw [closedBall_eq_preimage]

nonrec theorem exists_pos_lt_subset_b

Depends on / 依赖: isClosed, isCompact_closedBall, isCompact_closedBall.isClosed
-/
theorem isClosed_closedBall {x : E} {r : Real} : IsClosed (closedBall x r) :=
  isCompact_closedBall.isClosed

nonrec theorem closure_ball (x : E) {r : Real} (h : r != 0) : closure (ball x r) = closedBall x r := by
  rw [ball_eq_preimage]; rw [← toEuclidean.preimage_closure]; rw [closure_ball (toEuclidean x) h]; rw [closedBall_eq_preimage]

nonrec theorem exists_pos_lt_subset_ball {R : Real} {s : Set E} {x : E} (hR : 0 < R) (hs : IsClosed s)
    (h : s subseteq ball x R) : exists r in Ioo 0 R, s subseteq ball x r := by
  rw [ball_eq_preimage]; rw [← image_subset_iff] at h
  rcases exists_pos_lt_subset_ball hR (toEuclidean.isClosed_image.2 hs) h with ⟨r, hr, hsr⟩
  exact ⟨r, hr, image_subset_iff.1 hsr⟩

/--
theorem `nhds_basis_closedBall` / 定理 `nhds_basis_closedBall`

English:
theorem nhds_basis_closedBall
  given: {x : E}
  statement: (𝓝 x).HasBasis (fun r : Real => 0 < r) (closedBall x)
  proof: by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_closedBall.comap _

中文:
定理 nhds_basis_closedBall
  条件: {x : E}
  结论: (𝓝 x).有基 (fun r : 实数 => 0 < r) (closedBall x)
  证明: by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_closedBall.comap _

Depends on / 依赖: Metric, Metric.nhds_basis_closedBall.comap, nhds_basis_closedBall, nhds_eq_comap, toEuclidean, toEuclidean.toHomeomorph.nhds_eq_comap, toHomeomorph
-/
theorem nhds_basis_closedBall {x : E} : (𝓝 x).HasBasis (fun r : Real => 0 < r) (closedBall x) := by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_closedBall.comap _

/--
theorem `closedBall_mem_nhds` / 定理 `closedBall_mem_nhds`

English:
theorem closedBall_mem_nhds
  given: {x : E} {r : Real} (hr : 0 < r)
  statement: closedBall x r in 𝓝 x
  proof: nhds_basis_closedBall.mem_of_mem hr

中文:
定理 closedBall_mem_nhds
  条件: {x : E} {r : 实数} (hr : 0 < r)
  结论: closedBall x r in 𝓝 x
  证明: nhds_basis_closedBall.mem_of_mem hr

Depends on / 依赖: mem_of_mem, nhds_basis_closedBall, nhds_basis_closedBall.mem_of_mem
-/
theorem closedBall_mem_nhds {x : E} {r : Real} (hr : 0 < r) : closedBall x r in 𝓝 x :=
  nhds_basis_closedBall.mem_of_mem hr

/--
theorem `nhds_basis_ball` / 定理 `nhds_basis_ball`

English:
theorem nhds_basis_ball
  given: {x : E}
  statement: (𝓝 x).HasBasis (fun r : Real => 0 < r) (ball x)
  proof: by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_ball.comap _

中文:
定理 nhds_basis_ball
  条件: {x : E}
  结论: (𝓝 x).有基 (fun r : 实数 => 0 < r) (ball x)
  证明: by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_ball.comap _

Depends on / 依赖: Metric, Metric.nhds_basis_ball.comap, nhds_basis_ball, nhds_eq_comap, toEuclidean, toEuclidean.toHomeomorph.nhds_eq_comap, toHomeomorph
-/
theorem nhds_basis_ball {x : E} : (𝓝 x).HasBasis (fun r : Real => 0 < r) (ball x) := by
  rw [toEuclidean.toHomeomorph.nhds_eq_comap x]
  exact Metric.nhds_basis_ball.comap _

/--
theorem `ball_mem_nhds` / 定理 `ball_mem_nhds`

English:
theorem ball_mem_nhds
  given: {x : E} {r : Real} (hr : 0 < r)
  statement: ball x r in 𝓝 x
  proof: nhds_basis_ball.mem_of_mem hr

中文:
定理 ball_mem_nhds
  条件: {x : E} {r : 实数} (hr : 0 < r)
  结论: ball x r in 𝓝 x
  证明: nhds_basis_ball.mem_of_mem hr

Depends on / 依赖: mem_of_mem, nhds_basis_ball, nhds_basis_ball.mem_of_mem
-/
theorem ball_mem_nhds {x : E} {r : Real} (hr : 0 < r) : ball x r in 𝓝 x :=
  nhds_basis_ball.mem_of_mem hr

end Euclidean

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] {G : Type*} [NormedAddCommGroup G]
  [NormedSpace Real G] [FiniteDimensional Real G] {f g : F -> G} {n : Nat∞}

/--
theorem `ContDiff.euclidean_dist` / 定理 `ContDiff.euclidean_dist`

English:
theorem ContDiff.euclidean_dist
  given: (hf : ContDiff Real n f) (hg : ContDiff Real n g) (h : forall x, f x != g x)
  proof: by
  simp only [Euclidean.dist]
  apply ContDiff.dist Real
  exacts [(toEuclidean (E := G)).contDiff.comp hf,
    (toEuclidean (E := G)).contDiff.comp hg, fun x => toEuclidean.injective.ne (h x)]

中文:
定理 连续可微.euclidean_dist
  条件: (hf : 连续可微 实数 n f) (hg : 连续可微 实数 n g) (h : 对任意 x, f x != g x)
  证明: by
  simp only [Euclidean.dist]
  apply ContDiff.dist Real
  exacts [(toEuclidean (E := G)).contDiff.comp hf,
    (toEuclidean (E := G)).contDiff.comp hg, fun x => toEuclidean.injective.ne (h x)]

Depends on / 依赖: ContDiff, ContDiff.dist, Euclidean, Euclidean.dist, contDiff, contDiff.comp, exacts, injective, toEuclidean, toEuclidean.injective.ne
-/
theorem ContDiff.euclidean_dist (hf : ContDiff Real n f) (hg : ContDiff Real n g) (h : forall x, f x != g x) :
    ContDiff Real n fun x => Euclidean.dist (f x) (g x) := by
  simp only [Euclidean.dist]
  apply ContDiff.dist Real
  exacts [(toEuclidean (E := G)).contDiff.comp hf,
    (toEuclidean (E := G)).contDiff.comp hg, fun x => toEuclidean.injective.ne (h x)]
