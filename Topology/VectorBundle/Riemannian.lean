/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.Hom

/-! # Riemannian vector bundles

Given a real vector bundle over a topological space whose fibers are all endowed with an inner
product, we say that this bundle is Riemannian if the inner product depends continuously on the
base point.

We introduce a typeclass `[IsContinuousRiemannianBundle F E]` registering this property.
Under this assumption, we show that the inner product of two continuous maps into the same fibers
of the bundle is a continuous function.

If one wants to endow an existing vector bundle with a Riemannian metric, there is a subtlety:
the inner product space structure on the fibers should give rise to a topology on the fibers
which is defeq to the original one, to avoid diamonds. To do this, we introduce a
class `[RiemannianBundle E]` containing the data of an inner
product on the fibers defining the same topology as the original one. Given this class, we can
construct `NormedAddCommGroup` and `InnerProductSpace` instances on the fibers, compatible in a
defeq way with the initial topology. If the data used to register the instance `RiemannianBundle E`
depends continuously on the base point, we register automatically an instance of
`[IsContinuousRiemannianBundle F E]` (and similarly if the data is smooth).

The general theory should be built assuming `[IsContinuousRiemannianBundle F E]`, while the
`[RiemannianBundle E]` mechanism is only to build data in specific situations, for instance for
the tangent bundle. As instances related to Riemannian bundles are both costly and quite specific,
they are scoped to the `Bundle` namespace.

## Keywords
Vector bundle, Riemannian metric
-/

@[expose] public section

open Bundle ContinuousLinearMap Filter
open scoped Topology

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  {E : B -> Type*} [TopologicalSpace (TotalSpace F E)] [forall x, NormedAddCommGroup (E x)]
  [forall x, InnerProductSpace Real (E x)]
  [FiberBundle F E] [VectorBundle Real F E]

local notation "⟪" x ", " y "⟫" => inner Real x y

variable (F E) in
/--
Definition of `IsContinuousRiemannianBundle` / `IsContinuousRiemannianBundle` 的定义

English:
class IsContinuousRiemannianBundle
  parameters: : Prop where
  axioms and operations (1):
    - exists_continuous : exists g : (Π x, E x ->L[Real] E x ->L[Real] Real), Continuous (fun (x : B) => TotalSpace.mk' (F ->L[Real] F ->L[Real] Real) x (g x)) ∧ forall (x : B) (v w : E x), ⟪v, w⟫ = g x v w

中文:
类 IsContinuousRiemannianBundle
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_continuous : 存在 g : (Π x, E x ->L[实数] E x ->L[实数] 实数), Continuous (fun (x : B) => TotalSpace.mk' (F ->L[实数] F ->L[实数] 实数) x (g x)) ∧ 对任意 (x : B) (v w : E x), ⟪v, w⟫ = g x v w
-/
class IsContinuousRiemannianBundle : Prop where
  /-- There exists a bilinear form, depending continuously on the basepoint and defining the
  inner product in the fibers. This is expressed as an existence statement so that it is Prop-valued
  in terms of existing data, the inner product on the fibers and the fiber bundle structure. -/
  exists_continuous : exists g : (Π x, E x ->L[Real] E x ->L[Real] Real),
    Continuous (fun (x : B) => TotalSpace.mk' (F ->L[Real] F ->L[Real] Real) x (g x))
    ∧ forall (x : B) (v w : E x), ⟪v, w⟫ = g x v w

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace Real F₁]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsContinuousRiemannianBundle F₁ (Bundle.Trivial B F₁)
  body: by
  refine ⟨fun x => innerSL Real, ?_, fun x v w => rfl⟩
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  convert! continuousAt_const (y := innerSL Real)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

中文:
实例 :
  签名: IsContinuousRiemannianBundle F₁ (Bundle.Trivial B F₁)
  定义体: by
  refine ⟨fun x => innerSL Real, ?_, fun x v w => rfl⟩
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  convert! continuousAt_const (y := innerSL Real)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

Depends on / 依赖: FiberBundle, FiberBundle.continuousAt_totalSpace, continuousAt_const, continuousAt_id, continuousAt_totalSpace, continuous_iff_continuousAt, convert, hom_trivializationAt_apply, inCoordinates, innerSL
-/
instance : IsContinuousRiemannianBundle F₁ (Bundle.Trivial B F₁) := by
  refine ⟨fun x => innerSL Real, ?_, fun x v w => rfl⟩
  rw [continuous_iff_continuousAt]
  intro x
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  convert! continuousAt_const (y := innerSL Real)
  ext v w
  simp [hom_trivializationAt_apply, inCoordinates]

end Trivial

section Continuous

variable
  {M : Type*} [TopologicalSpace M] [h : IsContinuousRiemannianBundle F E]
  {b : M -> B} {v w : forall x, E (b x)} {s : Set M} {x : M}

/--
lemma `ContinuousWithinAt.inner_bundle` / 引理 `ContinuousWithinAt.inner_bundle`

English:
lemma ContinuousWithinAt.inner_bundle
  proof: by
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  have hf : ContinuousWithinAt b s x := by
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContinuousWithinAt
      (fun m => TotalSpace.mk' Real (E := Bundle.Trivial B Real) (b m) (g (b m) 

中文:
引理 ContinuousWithinAt.inner_bundle
  证明: by
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  have hf : ContinuousWithinAt b s x := by
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContinuousWithinAt
      (fun m => TotalSpace.mk' Real (E := Bundle.Trivial B Real) (b m) (g (b m) 

Depends on / 依赖: Bundle, Bundle.Trivial, ContinuousWithinAt, FiberBundle, FiberBundle.continuousWithinAt_totalSpace, TotalSpace, TotalSpace.mk, Trivial, comp_continuousWithinAt, continuousAt, continuousWithinAt_totalSpace, exists_continuous, g_cont, g_cont.continuousAt.comp_continuousWithinAt, h.exists_continuous
-/
lemma ContinuousWithinAt.inner_bundle
    (hv : ContinuousWithinAt (fun m => (v m : TotalSpace F E)) s x)
    (hw : ContinuousWithinAt (fun m => (w m : TotalSpace F E)) s x) :
    ContinuousWithinAt (fun m => ⟪v m, w m⟫) s x := by
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  have hf : ContinuousWithinAt b s x := by
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContinuousWithinAt
      (fun m => TotalSpace.mk' Real (E := Bundle.Trivial B Real) (b m) (g (b m) (v m) (w m))) s x :=
    (g_cont.continuousAt.comp_continuousWithinAt hf).clm_bundle_apply₂ (F₁ := F) (F₂ := F) hv hw
  simp only [FiberBundle.continuousWithinAt_totalSpace] at this
  exact this.2

/--
lemma `ContinuousAt.inner_bundle` / 引理 `ContinuousAt.inner_bundle`

English:
lemma ContinuousAt.inner_bundle
  proof: by
  simp only [← continuousWithinAt_univ] at hv hw ⊢
  exact ContinuousWithinAt.inner_bundle hv hw

中文:
引理 ContinuousAt.inner_bundle
  证明: by
  simp only [← continuousWithinAt_univ] at hv hw ⊢
  exact ContinuousWithinAt.inner_bundle hv hw

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.inner_bundle, continuousWithinAt_univ, inner_bundle
-/
lemma ContinuousAt.inner_bundle
    (hv : ContinuousAt (fun m => (v m : TotalSpace F E)) x)
    (hw : ContinuousAt (fun m => (w m : TotalSpace F E)) x) :
    ContinuousAt (fun b => ⟪v b, w b⟫) x := by
  simp only [← continuousWithinAt_univ] at hv hw ⊢
  exact ContinuousWithinAt.inner_bundle hv hw

/--
lemma `ContinuousOn.inner_bundle` / 引理 `ContinuousOn.inner_bundle`

English:
lemma ContinuousOn.inner_bundle
  proof: fun x hx => (hv x hx).inner_bundle (hw x hx)

中文:
引理 ContinuousOn.inner_bundle
  证明: fun x hx => (hv x hx).inner_bundle (hw x hx)

Depends on / 依赖: inner_bundle
-/
lemma ContinuousOn.inner_bundle
    (hv : ContinuousOn (fun m => (v m : TotalSpace F E)) s)
    (hw : ContinuousOn (fun m => (w m : TotalSpace F E)) s) :
    ContinuousOn (fun b => ⟪v b, w b⟫) s :=
  fun x hx => (hv x hx).inner_bundle (hw x hx)

/--
lemma `Continuous.inner_bundle` / 引理 `Continuous.inner_bundle`

English:
lemma Continuous.inner_bundle
  proof: by
  simp only [continuous_iff_continuousAt] at hv hw ⊢
  exact fun x => (hv x).inner_bundle (hw x)

中文:
引理 Continuous.inner_bundle
  证明: by
  simp only [continuous_iff_continuousAt] at hv hw ⊢
  exact fun x => (hv x).inner_bundle (hw x)

Depends on / 依赖: continuous_iff_continuousAt, inner_bundle
-/
lemma Continuous.inner_bundle
    (hv : Continuous (fun m => (v m : TotalSpace F E)))
    (hw : Continuous (fun m => (w m : TotalSpace F E))) :
    Continuous (fun b => ⟪v b, w b⟫) := by
  simp only [continuous_iff_continuousAt] at hv hw ⊢
  exact fun x => (hv x).inner_bundle (hw x)

variable (F E)

/--
lemma `eventually_norm_symmL_trivializationAt_self_comp_lt` / 引理 `eventually_norm_symmL_trivializationAt_self_comp_lt`

English:
lemma eventually_norm_symmL_trivializationAt_self_comp_lt
  given: (x : B) {r : Real} (hr : 1 < r)
  proof: by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w

中文:
引理 eventually_norm_symmL_trivializationAt_self_comp_lt
  条件: (x : B) {r : 实数} (hr : 1 < r)
  证明: by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w
-/
lemma eventually_norm_symmL_trivializationAt_self_comp_lt (x : B) {r : Real} (hr : 1 < r) :
    forallᶠ y in 𝓝 x, ‖((trivializationAt F E x).symmL Real x)
      ∘L ((trivializationAt F E x).continuousLinearMapAt Real y)‖ < r := by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w w`, where `w` is the image in the chart of a tangent vector `v` at `y`.
  Their difference is controlled by `δ ‖w‖ ^ 2` for any small `δ > 0`. To conclude, we argue that
  `‖w‖` is comparable to the norm inside the fiber over `x`, i.e., `g' x w w`, because there
  is a continuous linear equivalence between these two spaces by definition of vector bundles. -/
  obtain ⟨r', hr', r'r⟩ : exists r', 1 < r' ∧ r' < r := exists_between hr
  have h'x : x in (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let G := (trivializationAt F E x).continuousLinearEquivAt Real x h'x
  let C := (‖(G : E x ->L[Real] F)‖) ^ 2
  -- choose `δ` small enough that the computation below works when the metrics at `x` and `y`
  -- are `δ` close. When writing this proof, I have followed my nose in the computation, and
  -- recorded only in the end how small `δ` needs to be. The reader should skip the precise
  -- condition for now, as it doesn't give any useful insight.
  obtain ⟨δ, δpos, hδ⟩ : exists δ, 0 < δ ∧ (r' ^ 2)⁻¹ < 1 - δ * C := by
    have A : forallᶠ δ in 𝓝[>] (0 : Real), 0 < δ := self_mem_nhdsWithin
    have B : Tendsto (fun δ => 1 - δ * C) (𝓝[>] 0) (𝓝 (1 - 0 * C)) := by
      apply tendsto_inf_left
      exact tendsto_const_nhds.sub (tendsto_id.mul tendsto_const_nhds)
    have B' : forallᶠ δ in 𝓝[>] 0, (r' ^ 2)⁻¹ < 1 - δ * C := by
      apply (tendsto_order.1 B).1
      simpa using inv_lt_one_of_one_lt₀ (by nlinarith)
    exact (A.and B').exists
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  let g' : B -> F ->L[Real] F ->L[Real] Real := fun y =>
    inCoordinates F E (F ->L[Real] Real) (fun x => E x ->L[Real] Real) x y x y (g y)
  have hg' : ContinuousAt g' x := by
    have W := g_cont.continuousAt (x := x)
    simp only [continuousAt_hom_bundle] at W
    exact W.2
  have : forallᶠ y in 𝓝 x, dist (g' y) (g' x) < δ := by
    rw [Metric.continuousAt_iff'] at hg'
    apply hg' _ δpos
  filter_upwards [this, (trivializationAt F E x).open_baseSet.mem_nhds h'x] with y hy h'y
  have : ‖g' x - g' y‖ <= δ := by rw [← dist_eq_norm']; exact hy.le
  -- To show that the norm of the composition is bounded by `r'`, we start from a vector
  -- `‖v‖`. We will show that its image has a controlled norm.
  apply (opNorm_le_bound _ (by linarith) (fun v => ?_)).trans_lt r'r
  -- rewrite the norm of `‖v‖` and of its image in terms of norms in the model space
  let w := (trivializationAt F E x).continuousLinearMapAt Real y v
  suffices ‖((trivializationAt F E x).symmL Real x) w‖ ^ 2 <= r' ^ 2 * ‖v‖ ^ 2 from
    le_of_sq_le_sq (by simpa [mul_pow]) (by positivity)
  simp only [Trivialization.symmL_apply, mem_baseSet_trivializationAt,
    ← real_inner_self_eq_norm_sq, hg]
  have hgy : g y v v = g' y w w := by
    rw [inCoordinates_apply_eq₂ h'y h'y (Set.mem_univ _)]
    have A : ((trivializationAt F E x).symm y)
       ((trivializationAt F E x).linearMapAt Real y v) = v := by
      convert! ((trivializationAt F E x).continuousLinearEquivAt Real _ h'y).symm_apply_apply v
      simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'y]
    simp [A, w]
  have hgx : g x ((trivializationAt F E x).symm x w) ((trivializationAt F E x).symm x w) =
      g' x w w := by
    rw [inCoordinates_apply_eq₂ h'x h'x (Set.mem_univ _)]
    simp
  rw [hgx]; rw [hgy]
  -- get a good control for the norms of `w` in the model space, using continuity
  have : g' x w w <= δ * C * g' x w w + g' y w w := calc
        g' x w w
    _ = (g' x - g' y) w w + g' y w w := by simp
    _ <= ‖g' x - g' y‖ * ‖w‖ * ‖w‖ + g' y w w := by
      grw [← le_opNorm₂, ← Real.le_norm_self]
    _ <= δ * ‖w‖ ^ 2 + g' y w w := by
      rw [pow_two]; rw [mul_assoc]; gcongr
    _ <= δ * (‖(G : E x ->L[Real] F)‖ * ‖G.symm w‖) ^ 2 + g' y w w := by
      grw [← le_opNorm]
      simp
    _ = δ * C * ‖G.symm w‖ ^ 2 + g' y w w := by ring
    _ = δ * C * g x (G.symm w) (G.symm w) + g' y w w := by simp [← hg]
    _ = δ * C * g' x w w + g' y w w := by
      rw [← hgx]; rfl
  have : (1 - δ * C) * g' x w w <= g' y w w := by linarith
  rw [← (le_div_iff₀' (lt_of_le_of_lt (by positivity) hδ))]; rw [div_eq_inv_mul] at this
  grw [this]
  gcongr
  · rw [← hgy, ← hg, real_inner_self_eq_norm_sq]
    positivity
  · exact inv_le_of_inv_le₀ (by positivity) hδ.le

/--
lemma `eventually_norm_trivializationAt_lt` / 引理 `eventually_norm_trivializationAt_lt`

English:
lemma eventually_norm_trivializationAt_lt
  given: (x : B)
  proof: by
  refine ⟨(1 + ‖(trivializationAt F E x).continuousLinearMapAt Real x‖) * 2, by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_self_comp_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt Real x) ∘L
      ((trivializationAt F E x).s

中文:
引理 eventually_norm_trivializationAt_lt
  条件: (x : B)
  证明: by
  refine ⟨(1 + ‖(trivializationAt F E x).continuousLinearMapAt Real x‖) * 2, by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_self_comp_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt Real x) ∘L
      ((trivializationAt F E x).s

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, FiberBundle, FiberBundle.mem_baseSet_trivializationAt, Trivial, Trivialization, Trivialization.continuousLinearMapAt_apply, baseSet, continuousLinearMapAt, continuousLinearMapAt_apply, eventually_norm_symmL_trivializationAt_self_comp_lt, filter_upwards, mem_baseSet_trivializationAt, one_lt_two, trivializationAt
-/
lemma eventually_norm_trivializationAt_lt (x : B) :
    exists C > 0, forallᶠ y in 𝓝 x, ‖(trivializationAt F E x).continuousLinearMapAt Real y‖ < C := by
  refine ⟨(1 + ‖(trivializationAt F E x).continuousLinearMapAt Real x‖) * 2, by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_self_comp_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt Real x) ∘L
      ((trivializationAt F E x).symmL Real x) = ContinuousLinearMap.id _ _ := by
    ext v
    have h'x : x in (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
      mem_baseSet_trivializationAt, comp_apply, id_apply]
    convert! ((trivializationAt F E x).continuousLinearEquivAt Real _ h'x).apply_symm_apply v
    simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'x]
  have : (trivializationAt F E x).continuousLinearMapAt Real y =
    (ContinuousLinearMap.id _ _) ∘L ((trivializationAt F E x).continuousLinearMapAt Real y) := by simp
  grw [this, ← A, comp_assoc, opNorm_comp_le]
  gcongr
  linarith

/--
lemma `eventually_norm_symmL_trivializationAt_comp_self_lt` / 引理 `eventually_norm_symmL_trivializationAt_comp_self_lt`

English:
lemma eventually_norm_symmL_trivializationAt_comp_self_lt
  given: (x : B) {r : Real} (hr : 1 < r)
  proof: by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w

中文:
引理 eventually_norm_symmL_trivializationAt_comp_self_lt
  条件: (x : B) {r : 实数} (hr : 1 < r)
  证明: by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w
-/
lemma eventually_norm_symmL_trivializationAt_comp_self_lt (x : B) {r : Real} (hr : 1 < r) :
    forallᶠ y in 𝓝 x, ‖((trivializationAt F E x).symmL Real y)
      ∘L ((trivializationAt F E x).continuousLinearMapAt Real x)‖ < r := by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w w`, where `w` is the image in the chart of a tangent vector `v` at `x`.
  Their difference is controlled by `δ ‖w‖ ^ 2` for any small `δ > 0`. To conclude, we argue that
  `‖w‖` is comparable to the norm inside the fiber over `x`, i.e., `g' x w w`, because there
  is a continuous linear equivalence between these two spaces by definition of vector bundles. -/
  obtain ⟨r', hr', r'r⟩ : exists r', 1 < r' ∧ r' < r := exists_between hr
  have h'x : x in (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let G := (trivializationAt F E x).continuousLinearEquivAt Real x h'x
  let C := (‖(G : E x ->L[Real] F)‖) ^ 2
  -- choose `δ` small enough that the computation below works when the metrics at `x` and `y`
  -- are `δ` close. When writing this proof, I have followed my nose in the computation, and
  -- recorded only in the end how small `δ` needs to be. The reader should skip the precise
  -- condition for now, as it doesn't give any useful insight.
  obtain ⟨δ, δpos, h'δ⟩ : exists δ, 0 < δ ∧ (1 + δ * C) < r' ^ 2 := by
    have A : forallᶠ δ in 𝓝[>] (0 : Real), 0 < δ := self_mem_nhdsWithin
    have B : Tendsto (fun δ => 1 + δ * C) (𝓝[>] 0) (𝓝 (1 + 0 * C)) := by
      apply tendsto_inf_left
      exact tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    have B' : forallᶠ δ in 𝓝[>] 0, 1 + δ * C < r' ^ 2 := by
      apply (tendsto_order.1 B).2
      simpa using hr'.trans_le (le_abs_self _)
    exact (A.and B').exists
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  let g' : B -> F ->L[Real] F ->L[Real] Real := fun y =>
    inCoordinates F E (F ->L[Real] Real) (fun x => E x ->L[Real] Real) x y x y (g y)
  have hg' : ContinuousAt g' x := by
    have W := g_cont.continuousAt (x := x)
    simp only [continuousAt_hom_bundle] at W
    exact W.2
  have : forallᶠ y in 𝓝 x, dist (g' y) (g' x) < δ := by
    rw [Metric.continuousAt_iff'] at hg'
    apply hg' _ δpos
  filter_upwards [this, (trivializationAt F E x).open_baseSet.mem_nhds h'x] with y hy h'y
  have : ‖g' y - g' x‖ <= δ := by rw [← dist_eq_norm]; exact hy.le
  -- To show that the norm of the composition is bounded by `r'`, we start from a vector
  -- `‖v‖`. We will show that its image has a controlled norm.
  apply (opNorm_le_bound _ (by linarith) (fun v => ?_)).trans_lt r'r
  -- rewrite the norm of `‖v‖` and of its image in terms of norms in the model space
  let w := (trivializationAt F E x).continuousLinearMapAt Real x v
  suffices ‖((trivializationAt F E x).symmL Real y) w‖ ^ 2 <= r' ^ 2 * ‖v‖ ^ 2 from
    le_of_sq_le_sq (by simpa [mul_pow]) (by positivity)
  simp only [Trivialization.symmL_apply, h'y, ← real_inner_self_eq_norm_sq, hg]
  have hgx : g x v v = g' x w w := by
    rw [inCoordinates_apply_eq₂ h'x h'x (Set.mem_univ _)]
    have A : ((trivializationAt F E x).symm x)
       ((trivializationAt F E x).linearMapAt Real x v) = v := by
      convert! ((trivializationAt F E x).continuousLinearEquivAt Real _ h'x).symm_apply_apply v
      simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'x]
    simp [A, w]
  have hgy : g y ((trivializationAt F E x).symm y w) ((trivializationAt F E x).symm y w)
      = g' y w w := by
    rw [inCoordinates_apply_eq₂ h'y h'y (Set.mem_univ _)]
    simp
  rw [hgx]; rw [hgy]
  -- get a good control for the norms of `w` in the model space, using continuity
  calc g' y w w
    _ = (g' y - g' x) w w + g' x w w := by simp
    _ <= ‖g' y - g' x‖ * ‖w‖ * ‖w‖ + g' x w w := by
      grw [← le_opNorm₂, ← Real.le_norm_self]
    _ <= δ * ‖w‖ ^ 2 + g' x w w := by
      rw [pow_two]; rw [mul_assoc]; gcongr
    _ <= δ * (‖(G : E x ->L[Real] F)‖ * ‖G.symm w‖) ^ 2 + g' x w w := by
      grw [← le_opNorm]
      simp
    _ = δ * C * ‖G.symm w‖ ^ 2 + g' x w w := by ring
    _ = δ * C * g x (G.symm w) (G.symm w) + g' x w w := by simp [← hg]
    _ = δ * C * g' x w w + g' x w w := by
      congr
      rw [inCoordinates_apply_eq₂ h'x h'x (Set.mem_univ _)]
      simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
        LinearMap.id_coe, id_eq, w]
      rfl
    _ = (1 + δ * C) * g' x w w := by ring
    _ <= r' ^ 2 * g' x w w := by
      gcongr
      rw [← hgx]; rw [← hg]; rw [real_inner_self_eq_norm_sq]
      positivity

/--
lemma `eventually_norm_symmL_trivializationAt_lt` / 引理 `eventually_norm_symmL_trivializationAt_lt`

English:
lemma eventually_norm_symmL_trivializationAt_lt
  given: (x : B)
  proof: by
  refine ⟨2 * (1 + ‖(trivializationAt F E x).symmL Real x‖), by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt Real x) ∘L
      ((trivializationAt F E x).symmL Real x) = C

中文:
引理 eventually_norm_symmL_trivializationAt_lt
  条件: (x : B)
  证明: by
  refine ⟨2 * (1 + ‖(trivializationAt F E x).symmL Real x‖), by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt Real x) ∘L
      ((trivializationAt F E x).symmL Real x) = C

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, FiberBundle, FiberBundle.mem_baseSet_trivializationAt, Trivialization, Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_ap, baseSet, continuousLinearMapAt, continuousLinearMapAt_apply, eventually_norm_symmL_trivializationAt_comp_self_lt, filter_upwards, mem_baseSet_trivializationAt, one_lt_two, symmL_ap, trivializationAt
-/
lemma eventually_norm_symmL_trivializationAt_lt (x : B) :
    exists C > 0, forallᶠ y in 𝓝 x, ‖(trivializationAt F E x).symmL Real y‖ < C := by
  refine ⟨2 * (1 + ‖(trivializationAt F E x).symmL Real x‖), by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt Real x) ∘L
      ((trivializationAt F E x).symmL Real x) = ContinuousLinearMap.id _ _ := by
    ext v
    have h'x : x in (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
      mem_baseSet_trivializationAt, comp_apply, id_apply]
    convert! ((trivializationAt F E x).continuousLinearEquivAt Real _ h'x).apply_symm_apply v
    simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'x]
  have : (trivializationAt F E x).symmL Real y =
     ((trivializationAt F E x).symmL Real y) ∘L (ContinuousLinearMap.id _ _) := by simp
  grw [this, ← A, ← comp_assoc, opNorm_comp_le]
  gcongr
  linarith

end Continuous

namespace Bundle

section Construction

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  {E : B -> Type*} [TopologicalSpace (TotalSpace F E)]
  [forall b, TopologicalSpace (E b)] [forall b, AddCommGroup (E b)] [forall b, Module Real (E b)]
  [forall b, IsTopologicalAddGroup (E b)] [forall b, ContinuousConstSMul Real (E b)]
  [FiberBundle F E] [VectorBundle Real F E]

open Bornology

variable (E) in
/--
Definition of `RiemannianMetric` / `RiemannianMetric` 的定义

English:
structure RiemannianMetric
  parameters: where
  axioms and operations (5):
    - inner((b : B)) : E b ->L[Real] E b ->L[Real] Real
    - symm((b : B) (v w : E b)) : inner b v w = inner b w v
    - pos((b : B) (v : E b) (hv : v != 0)) : 0 < inner b v v
    - continuousAt((b : B)) : ContinuousAt (fun (v : E b) => inner b v v) 0
    - isVonNBounded((b : B)) : IsVonNBounded Real {v : E b | inner b v v < 1}

中文:
结构 RiemannianMetric
  参数: where
  公理与运算 (5 个):
    - inner((b : B)) : E b ->L[实数] E b ->L[实数] 实数
    - symm((b : B) (v w : E b)) : inner b v w = inner b w v
    - pos((b : B) (v : E b) (hv : v != 0)) : 0 < inner b v v
    - continuousAt((b : B)) : ContinuousAt (fun (v : E b) => inner b v v) 0
    - isVonNBounded((b : B)) : IsVonNBounded 实数 {v : E b | inner b v v < 1}
-/
structure RiemannianMetric where
  /-- The inner product along the fibers of the bundle. -/
  inner (b : B) : E b ->L[Real] E b ->L[Real] Real
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v != 0) : 0 < inner b v v
  /-- The continuity at `0` is automatic when `E b` is isomorphic to a normed space, but since
  we are not making this assumption here we have to include it. -/
  continuousAt (b : B) : ContinuousAt (fun (v : E b) => inner b v v) 0
  isVonNBounded (b : B) : IsVonNBounded Real {v : E b | inner b v v < 1}

/--
Definition of `RiemannianMetric.toCore` / `RiemannianMetric.toCore` 的定义

English:
definition RiemannianMetric.toCore
  signature: (g : RiemannianMetric E) (b : B)
  body: g.inner b v w
  conj_inner_symm v w := g.symm b w v
  re_inner_nonneg v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · simpa using (g.pos b v hv).le
  add_left v w x := by simp
  smul_left c v := by simp
  definite v h := by contrapose! h; exact (g.pos b v h).ne'

中文:
定义 RiemannianMetric.toCore
  签名: (g : RiemannianMetric E) (b : B)
  定义体: g.inner b v w
  conj_inner_symm v w := g.symm b w v
  re_inner_nonneg v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · simpa using (g.pos b v hv).le
  add_left v w x := by simp
  smul_left c v := by simp
  definite v h := by contrapose! h; exact (g.pos b v h).ne'
-/
@[reducible] noncomputable def RiemannianMetric.toCore (g : RiemannianMetric E) (b : B) :
    InnerProductSpace.Core Real (E b) where
  inner v w := g.inner b v w
  conj_inner_symm v w := g.symm b w v
  re_inner_nonneg v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · simpa using (g.pos b v hv).le
  add_left v w x := by simp
  smul_left c v := by simp
  definite v h := by contrapose! h; exact (g.pos b v h).ne'

variable (E) in
/--
Definition of `RiemannianBundle` / `RiemannianBundle` 的定义

English:
class RiemannianBundle
  parameters: where
  axioms and operations (1):
    - g : RiemannianMetric E

中文:
类 RiemannianBundle
  参数: where
  公理与运算 (1 个):
    - g : RiemannianMetric E
-/
class RiemannianBundle where
  /-- The family of inner products on the fibers -/
  g : RiemannianMetric E

/-- A fiber in a bundle satisfying the `[RiemannianBundle E]` typeclass inherits
a `NormedAddCommGroup` structure.

The normal priority for an instance which always applies like this one should be 100.
We use 80 as this is rather specialized, so we want other paths to be tried first typically.
As this instance is quite specific and very costly because of higher-order unification, we
also scope it to the `Bundle` namespace. -/
noncomputable scoped instance (priority := 80)
    {B : Type*} {E : B -> Type*} [(b : B) -> TopologicalSpace (E b)]
    [(b : B) -> AddCommGroup (E b)] [(b : B) -> Module Real (E b)]
    /- We are careful about the parameter order, putting `RiemannianBundle E`
    before `IsTopologicalAddGroup` to avoid the following loop: to put a `IsTopologicalAddGroup`
    structure on `E b`, one tries to find a `NormedAddCommGroup`, then one tries to apply the
    current instance. If `IsTopologicalAddGroup (E b)` were before `RiemannianBundle`, then one
    would try to find a `IsTopologicalAddGroup` to apply the instance, and loop.
    Normally, loops are detected by typeclass inference but here it is not the case as the loop is
    at different depth levels. See lean4#13063. -/
    [h : RiemannianBundle E] [forall (b : B), IsTopologicalAddGroup (E b)]
    [forall (b : B), ContinuousConstSMul Real (E b)] (b : B) :
    NormedAddCommGroup (E b) := fast_instance%
  (h.g.toCore b).toNormedAddCommGroupOfTopology (h.g.continuousAt b) (h.g.isVonNBounded b)

/-- A fiber in a bundle satisfying the `[RiemannianBundle E]` typeclass inherits
an `InnerProductSpace ℝ` structure.

The normal priority for an instance which always applies like this one should be 100.
We use 80 as this is rather specialized, so we want other paths to be tried first typically.
As this instance is quite specific and very costly because of higher-order unification, we
also scope it to the `Bundle` namespace. -/
noncomputable scoped instance (priority := 80)
    {B : Type*} {E : B -> Type*} [(b : B) -> TopologicalSpace (E b)]
    [(b : B) -> AddCommGroup (E b)] [(b : B) -> Module Real (E b)]
    [h : RiemannianBundle E] [forall (b : B), IsTopologicalAddGroup (E b)]
    [forall (b : B), ContinuousConstSMul Real (E b)] (b : B) :
    InnerProductSpace Real (E b) := fast_instance%
  .ofCoreOfTopology (h.g.toCore b) (h.g.continuousAt b) (h.g.isVonNBounded b)

variable (F E) in
/--
Definition of `ContinuousRiemannianMetric` / `ContinuousRiemannianMetric` 的定义

English:
structure ContinuousRiemannianMetric
  parameters: where
  axioms and operations (5):
    - inner((b : B)) : E b ->L[Real] E b ->L[Real] Real
    - symm((b : B) (v w : E b)) : inner b v w = inner b w v
    - pos((b : B) (v : E b) (hv : v != 0)) : 0 < inner b v v
    - isVonNBounded((b : B)) : IsVonNBounded Real {v : E b | inner b v v < 1}
    - continuous : Continuous (fun (b : B) => TotalSpace.mk' (F ->L[Real] F ->L[Real] Real) b (inner b))

中文:
结构 ContinuousRiemannianMetric
  参数: where
  公理与运算 (5 个):
    - inner((b : B)) : E b ->L[实数] E b ->L[实数] 实数
    - symm((b : B) (v w : E b)) : inner b v w = inner b w v
    - pos((b : B) (v : E b) (hv : v != 0)) : 0 < inner b v v
    - isVonNBounded((b : B)) : IsVonNBounded 实数 {v : E b | inner b v v < 1}
    - continuous : Continuous (fun (b : B) => TotalSpace.mk' (F ->L[实数] F ->L[实数] 实数) b (inner b))
-/
structure ContinuousRiemannianMetric where
  /-- The inner product along the fibers of the bundle. -/
  inner (b : B) : E b ->L[Real] E b ->L[Real] Real
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v != 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded Real {v : E b | inner b v v < 1}
  continuous : Continuous (fun (b : B) => TotalSpace.mk' (F ->L[Real] F ->L[Real] Real) b (inner b))

/--
Definition of `ContinuousRiemannianMetric.toRiemannianMetric` / `ContinuousRiemannianMetric.toRiemannianMetric` 的定义

English:
definition ContinuousRiemannianMetric.toRiemannianMetric
  signature: (g : ContinuousRiemannianMetric F E)
  body: g.inner
  symm := g.symm
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  continuousAt b := by
    -- Continuity of bilinear maps is only true on normed spaces. As `F` is a normed space by
    -- assumption, we transfer everything to `F` and argue there.
    let e : E b ≃L[Real] F := Trivializati

中文:
定义 ContinuousRiemannianMetric.toRiemannianMetric
  签名: (g : ContinuousRiemannianMetric F E)
  定义体: g.inner
  symm := g.symm
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  continuousAt b := by
    -- Continuity of bilinear maps is only true on normed spaces. As `F` is a normed space by
    -- assumption, we transfer everything to `F` and argue there.
    let e : E b ≃L[Real] F := Trivializati

Depends on / 依赖: g.inner
-/
def ContinuousRiemannianMetric.toRiemannianMetric (g : ContinuousRiemannianMetric F E) :
    RiemannianMetric E where
  inner := g.inner
  symm := g.symm
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  continuousAt b := by
    -- Continuity of bilinear maps is only true on normed spaces. As `F` is a normed space by
    -- assumption, we transfer everything to `F` and argue there.
    let e : E b ≃L[Real] F := Trivialization.continuousLinearEquivAt Real (trivializationAt F E b) _
      (FiberBundle.mem_baseSet_trivializationAt' b)
    let m : (E b ->L[Real] E b ->L[Real] Real) ≃L[Real] (F ->L[Real] F ->L[Real] Real) :=
      e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl Real Real))
    have A (v : E b) : g.inner b v v = ((fun w => m (g.inner b) w w) ∘ e) v := by simp [m]
    simp only [A]
    fun_prop

/-- If a Riemannian bundle structure is defined using `g.toRiemannianMetric` where `g` is
a `ContinuousRiemannianMetric`, then we make sure typeclass inference can infer automatically
that the bundle is a continuous Riemannian bundle. -/
instance (g : ContinuousRiemannianMetric F E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩;
    IsContinuousRiemannianBundle F E := by
  let : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  exact ⟨⟨g.inner, g.continuous, fun b v w => rfl⟩⟩

end Construction

end Bundle
