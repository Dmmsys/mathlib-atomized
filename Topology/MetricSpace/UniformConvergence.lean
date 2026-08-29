/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.CompleteLattice.Group
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-! # Metric structure on `α →ᵤ β` and `α →ᵤ[𝔖] β` for finite `𝔖`

When `β` is a (pseudo, extended) metric space it is a uniform space, and therefore we may
consider the type `α →ᵤ β` of functions equipped with the topology of uniform convergence. The
natural (pseudo, extended) metric on this space is given by `fun f g ↦ ⨆ x, edist (f x) (g x)`,
and this induces the existing uniformity. Unless `β` is a bounded space, this will not be a (pseudo)
metric space (except in the trivial case where `α` is empty).

When `𝔖 : Set (Set α)` is a collection of subsets, we may equip the space of functions with the
(pseudo, extended) metric `fun f g ↦ ⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)`. *However*, this only induces
the pre-existing uniformity on `α →ᵤ[𝔖] β` if `𝔖` is finite, and hence we only have an instance in
that case. Nevertheless, this still covers the most important case, such as when `𝔖` is a singleton.

Furthermore, we note that this is essentially a mathematical obstruction, not a technical one:
indeed, the uniformity of `α →ᵤ[𝔖] β` is countably generated only when there is a sequence
`t : ℕ → Finset (Set α)` such that, for each `n`, `t n ⊆ 𝔖`, `fun n ↦ Finset.sup (t n)` is monotone
and for every `s ∈ 𝔖`, there is some `n` such that `s ⊆ Finset.sup (t n)` (see
`UniformOnFun.isCountablyGenerated_uniformity`). So, while the `𝔖` for which `α →ᵤ[𝔖] β` is
metrizable include some non-finite `𝔖`, there are some `𝔖` which are not metrizable, and moreover,
it is only when `𝔖` is finite that `⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)` is a metric which induces the
uniformity.

There are a few advantages of equipping this space with this metric structure.

1. A function `f : X → α →ᵤ β` is Lipschitz in this metric if and only if for every `a : α` it is
  Lipschitz in the first variable with the same Lipschitz constant.
2. It provides a natural setting in which one can talk about the metrics on `α →ᵇ β` or, when
  `α` is compact, `C(α, β)`, relative to their underlying bare functions.
-/

public section

variable {α β γ : Type*} [PseudoEMetricSpace γ]
open scoped UniformConvergence NNReal ENNReal
open Filter Topology Uniformity

namespace UniformFun

section EMetric

variable [PseudoEMetricSpace β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EDist (α ->ᵤ β)
  body: ⨆ x, edist (toFun f x) (toFun g x)

中文:
实例 :
  签名: EDist (α ->ᵤ β)
  定义体: ⨆ x, edist (toFun f x) (toFun g x)
-/
noncomputable instance : EDist (α ->ᵤ β) where
  edist f g := ⨆ x, edist (toFun f x) (toFun g x)

/--
lemma `edist_def` / 引理 `edist_def`

English:
lemma edist_def
  given: (f g : α ->ᵤ β)
  proof: rfl

中文:
引理 edist_def
  条件: (f g : α ->ᵤ β)
  证明: rfl
-/
lemma edist_def (f g : α ->ᵤ β) :
    edist f g = ⨆ x, edist (toFun f x) (toFun g x) :=
  rfl

/--
lemma `edist_le` / 引理 `edist_le`

English:
lemma edist_le
  given: {f g : α ->ᵤ β} {C : Real>=0∞}
  proof: iSup_le_iff

中文:
引理 edist_le
  条件: {f g : α ->ᵤ β} {C : 实数>=0∞}
  证明: iSup_le_iff

Depends on / 依赖: iSup_le_iff
-/
lemma edist_le {f g : α ->ᵤ β} {C : Real>=0∞} :
    edist f g <= C ↔ forall x, edist (toFun f x) (toFun g x) <= C :=
  iSup_le_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoEMetricSpace (α ->ᵤ β)
  body: by simp [edist_def]
  edist_comm := by simp [edist_def, edist_comm]
  edist_triangle f₁ f₂ f₃ := calc
    ⨆ x, edist (f₁ x) (f₃ x) <= ⨆ x, edist (f₁ x) (f₂ x) + edist (f₂ x) (f₃ x) :=
      iSup_mono fun _ => edist_triangle _ _ _
    _ <= (⨆ x, edist (f₁ x) (f₂ x)) + (⨆ x, edist (f₂ x) (f₃ x)) := iSup_add_le _ _
  toUniformSpace := inferInstance
  uniformity_edist := by
    suffices 𝓤 (α ->ᵤ β) = comap (fun x => edist x.1 x.2) (𝓝 0) by
      simp [this, ENNReal.nhds_zero_basis.comap _ |>.eq_biInf, Set.Iio]
    rw [ENNReal.nhds_zero_basis_Iic.comap _ |>.eq_biInf]
    rw [UniformFun.hasBasis_uniformity_of_basis α β uniformity_basis_edist_le |>.eq_biInf]
    simp [UniformFun.gen, edist_le, Set.Iic]

中文:
实例 :
  签名: PseudoEMetric空间 (α ->ᵤ β)
  定义体: by simp [edist_def]
  edist_comm := by simp [edist_def, edist_comm]
  edist_triangle f₁ f₂ f₃ := calc
    ⨆ x, edist (f₁ x) (f₃ x) <= ⨆ x, edist (f₁ x) (f₂ x) + edist (f₂ x) (f₃ x) :=
      iSup_mono fun _ => edist_triangle _ _ _
    _ <= (⨆ x, edist (f₁ x) (f₂ x)) + (⨆ x, edist (f₂ x) (f₃ x)) := iSup_add_le _ _
  toUniformSpace := inferInstance
  uniformity_edist := by
    suffices 𝓤 (α ->ᵤ β) = comap (fun x => edist x.1 x.2) (𝓝 0) by
      simp [this, ENNReal.nhds_zero_basis.comap _ |>.eq_biInf, Set.Iio]
    rw [ENNReal.nhds_zero_basis_Iic.comap _ |>.eq_biInf]
    rw [UniformFun.hasBasis_uniformity_of_basis α β uniformity_basis_edist_le |>.eq_biInf]
    simp [UniformFun.gen, edist_le, Set.Iic]

Depends on / 依赖: ENNReal, ENNReal.nhds_zer, ENNReal.nhds_zero_basis.comap, Set.Iio, edist_comm, edist_def, edist_triangle, eq_biInf, iSup_add_le, iSup_mono, nhds_zer, nhds_zero_basis, toUniformSpace, uniformity_edist
-/
noncomputable instance : PseudoEMetricSpace (α ->ᵤ β) where
  edist_self := by simp [edist_def]
  edist_comm := by simp [edist_def, edist_comm]
  edist_triangle f₁ f₂ f₃ := calc
    ⨆ x, edist (f₁ x) (f₃ x) <= ⨆ x, edist (f₁ x) (f₂ x) + edist (f₂ x) (f₃ x) :=
      iSup_mono fun _ => edist_triangle _ _ _
    _ <= (⨆ x, edist (f₁ x) (f₂ x)) + (⨆ x, edist (f₂ x) (f₃ x)) := iSup_add_le _ _
  toUniformSpace := inferInstance
  uniformity_edist := by
    suffices 𝓤 (α ->ᵤ β) = comap (fun x => edist x.1 x.2) (𝓝 0) by
      simp [this, ENNReal.nhds_zero_basis.comap _ |>.eq_biInf, Set.Iio]
    rw [ENNReal.nhds_zero_basis_Iic.comap _ |>.eq_biInf]
    rw [UniformFun.hasBasis_uniformity_of_basis α β uniformity_basis_edist_le |>.eq_biInf]
    simp [UniformFun.gen, edist_le, Set.Iic]

noncomputable instance {β : Type*} [EMetricSpace β] : EMetricSpace (α ->ᵤ β) :=
  .ofT0PseudoEMetricSpace _

/--
lemma `lipschitzWith_iff` / 引理 `lipschitzWith_iff`

English:
lemma lipschitzWith_iff
  given: {f : γ -> α ->ᵤ β} {K : Real>=0}
  proof: by
  simp [LipschitzWith, edist_le, forall_comm (α := α)]

中文:
引理 lipschitzWith_iff
  条件: {f : γ -> α ->ᵤ β} {K : 实数>=0}
  证明: by
  simp [LipschitzWith, edist_le, forall_comm (α := α)]

Depends on / 依赖: LipschitzWith, edist_le, forall_comm
-/
lemma lipschitzWith_iff {f : γ -> α ->ᵤ β} {K : Real>=0} :
    LipschitzWith K f ↔ forall c, LipschitzWith K (fun x => toFun (f x) c) := by
  simp [LipschitzWith, edist_le, forall_comm (α := α)]

/--
lemma `lipschitzWith_ofFun_iff` / 引理 `lipschitzWith_ofFun_iff`

English:
lemma lipschitzWith_ofFun_iff
  given: {f : γ -> α -> β} {K : Real>=0}
  proof: lipschitzWith_iff

中文:
引理 lipschitzWith_ofFun_iff
  条件: {f : γ -> α -> β} {K : 实数>=0}
  证明: lipschitzWith_iff

Depends on / 依赖: lipschitzWith_iff
-/
lemma lipschitzWith_ofFun_iff {f : γ -> α -> β} {K : Real>=0} :
    LipschitzWith K (fun x => ofFun (f x)) ↔ forall c, LipschitzWith K (f · c) :=
  lipschitzWith_iff

/--
lemma `_root_.LipschitzWith.uniformEquicontinuous` / 引理 `_root_.LipschitzWith.uniformEquicontinuous`

English:
lemma _root_.LipschitzWith.uniformEquicontinuous
  statement: (f : α -> γ -> β) (K : Real>=0)
  proof: by
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [← lipschitzWith_ofFun_iff] at h
  exact h.uniformContinuous

中文:
引理 _root_.LipschitzWith.uniformEquicontinuous
  结论: (f : α -> γ -> β) (K : 实数>=0)
  证明: by
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [← lipschitzWith_ofFun_iff] at h
  exact h.uniformContinuous

Depends on / 依赖: h.uniformContinuous, lipschitzWith_ofFun_iff, uniformContinuous, uniformEquicontinuous_iff_uniformContinuous
-/
lemma _root_.LipschitzWith.uniformEquicontinuous (f : α -> γ -> β) (K : Real>=0)
    (h : forall c, LipschitzWith K (f c)) : UniformEquicontinuous f := by
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [← lipschitzWith_ofFun_iff] at h
  exact h.uniformContinuous

/--
lemma `lipschitzOnWith_iff` / 引理 `lipschitzOnWith_iff`

English:
lemma lipschitzOnWith_iff
  given: {f : γ -> α ->ᵤ β} {K : Real>=0} {s : Set γ}
  proof: by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

中文:
引理 lipschitzOnWith_iff
  条件: {f : γ -> α ->ᵤ β} {K : 实数>=0} {s : 集合 γ}
  证明: by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

Depends on / 依赖: lipschitzOnWith_iff_restrict, lipschitzWith_iff
-/
lemma lipschitzOnWith_iff {f : γ -> α ->ᵤ β} {K : Real>=0} {s : Set γ} :
    LipschitzOnWith K f s ↔ forall c, LipschitzOnWith K (fun x => toFun (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

/--
lemma `lipschitzOnWith_ofFun_iff` / 引理 `lipschitzOnWith_ofFun_iff`

English:
lemma lipschitzOnWith_ofFun_iff
  given: {f : γ -> α -> β} {K : Real>=0} {s : Set γ}
  proof: lipschitzOnWith_iff

中文:
引理 lipschitzOnWith_ofFun_iff
  条件: {f : γ -> α -> β} {K : 实数>=0} {s : 集合 γ}
  证明: lipschitzOnWith_iff

Depends on / 依赖: lipschitzOnWith_iff
-/
lemma lipschitzOnWith_ofFun_iff {f : γ -> α -> β} {K : Real>=0} {s : Set γ} :
    LipschitzOnWith K (fun x => ofFun (f x)) s ↔ forall c, LipschitzOnWith K (f · c) s :=
  lipschitzOnWith_iff

/--
lemma `_root_.LipschitzOnWith.uniformEquicontinuousOn` / 引理 `_root_.LipschitzOnWith.uniformEquicontinuousOn`

English:
lemma _root_.LipschitzOnWith.uniformEquicontinuousOn
  statement: (f : α -> γ -> β) (K : Real>=0) {s : Set γ}
  proof: by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]
  rw [← lipschitzOnWith_ofFun_iff] at h
  exact h.uniformContinuousOn

中文:
引理 _root_.LipschitzOnWith.uniformEquicontinuousOn
  结论: (f : α -> γ -> β) (K : 实数>=0) {s : 集合 γ}
  证明: by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]
  rw [← lipschitzOnWith_ofFun_iff] at h
  exact h.uniformContinuousOn

Depends on / 依赖: h.uniformContinuousOn, lipschitzOnWith_ofFun_iff, uniformContinuousOn, uniformEquicontinuousOn_iff_uniformContinuousOn
-/
lemma _root_.LipschitzOnWith.uniformEquicontinuousOn (f : α -> γ -> β) (K : Real>=0) {s : Set γ}
    (h : forall c, LipschitzOnWith K (f c) s) : UniformEquicontinuousOn f s := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]
  rw [← lipschitzOnWith_ofFun_iff] at h
  exact h.uniformContinuousOn

/--
lemma `edist_eval_le` / 引理 `edist_eval_le`

English:
lemma edist_eval_le
  given: {f g : α ->ᵤ β} {x : α}
  proof: edist_le.mp le_rfl x

中文:
引理 edist_eval_le
  条件: {f g : α ->ᵤ β} {x : α}
  证明: edist_le.mp le_rfl x

Depends on / 依赖: edist_le, edist_le.mp, le_rfl
-/
lemma edist_eval_le {f g : α ->ᵤ β} {x : α} :
    edist (toFun f x) (toFun g x) <= edist f g :=
  edist_le.mp le_rfl x

/--
lemma `lipschitzWith_eval` / 引理 `lipschitzWith_eval`

English:
lemma lipschitzWith_eval
  given: (x : α)
  proof: by
  intro f g
  simpa using edist_eval_le

中文:
引理 lipschitzWith_eval
  条件: (x : α)
  证明: by
  intro f g
  simpa using edist_eval_le

Depends on / 依赖: edist_eval_le
-/
lemma lipschitzWith_eval (x : α) :
    LipschitzWith 1 (fun f : α ->ᵤ β => toFun f x) := by
  intro f g
  simpa using edist_eval_le

end EMetric

section Metric

variable [PseudoMetricSpace β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedSpace
  signature: β] : PseudoMetricSpace (α ->ᵤ β)
  body: PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g => ⨆ x, dist (toFun f x) (toFun g x))
    (fun _ _ => Real.iSup_nonneg fun i => dist_nonneg)
    fun f g => by
      cases isEmpty_or_nonempty α
      · simp [edist_def]
have : BddAbove .range fun x => dist (toFun f x) (toFun g x) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      exact ENNReal.eq_of_forall_le_nnreal_iff fun r => by simp [edist_def, ciSup_le_iff this]

中文:
实例 [有界空间
  签名: β] : 伪度量空间 (α ->ᵤ β)
  定义体: PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g => ⨆ x, dist (toFun f x) (toFun g x))
    (fun _ _ => Real.iSup_nonneg fun i => dist_nonneg)
    fun f g => by
      cases isEmpty_or_nonempty α
      · simp [edist_def]
have : BddAbove .range fun x => dist (toFun f x) (toFun g x) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      exact ENNReal.eq_of_forall_le_nnreal_iff fun r => by simp [edist_def, ciSup_le_iff this]

Depends on / 依赖: BddAbove, BoundedSpace, BoundedSpace.bounded_univ.ediam_ne_top, ENNReal, ENNReal.ofReal_le_iff_le_toReal, Metric, Metric.ediam, Metric.edist_le_ediam_of_mem, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, Real.iSup_nonneg, bounded_univ, contextual, dist_nonneg, ediam_ne_top, edist_def, edist_dist, edist_le_ediam_of_mem, eq_comm, iSup_nonneg
-/
noncomputable instance [BoundedSpace β] : PseudoMetricSpace (α ->ᵤ β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g => ⨆ x, dist (toFun f x) (toFun g x))
    (fun _ _ => Real.iSup_nonneg fun i => dist_nonneg)
    fun f g => by
      cases isEmpty_or_nonempty α
      · simp [edist_def]
have : BddAbove .range fun x => dist (toFun f x) (toFun g x) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      exact ENNReal.eq_of_forall_le_nnreal_iff fun r => by simp [edist_def, ciSup_le_iff this]

/--
lemma `dist_def` / 引理 `dist_def`

English:
lemma dist_def
  given: [BoundedSpace β] (f g : α ->ᵤ β)
  proof: rfl

中文:
引理 dist_def
  条件: [有界空间 β] (f g : α ->ᵤ β)
  证明: rfl
-/
lemma dist_def [BoundedSpace β] (f g : α ->ᵤ β) :
    dist f g = ⨆ x, dist (toFun f x) (toFun g x) :=
  rfl

/--
lemma `dist_le` / 引理 `dist_le`

English:
lemma dist_le
  given: [BoundedSpace β] {f g : α ->ᵤ β} {C : Real} (hC : 0 <= C)
  proof: by
  simp_rw [dist_edist, ← ENNReal.le_ofReal_iff_toReal_le (edist_ne_top _ _) hC, edist_le]

中文:
引理 dist_le
  条件: [有界空间 β] {f g : α ->ᵤ β} {C : 实数} (hC : 0 <= C)
  证明: by
  simp_rw [dist_edist, ← ENNReal.le_ofReal_iff_toReal_le (edist_ne_top _ _) hC, edist_le]

Depends on / 依赖: ENNReal, ENNReal.le_ofReal_iff_toReal_le, dist_edist, edist_le, edist_ne_top, le_ofReal_iff_toReal_le, simp_rw
-/
lemma dist_le [BoundedSpace β] {f g : α ->ᵤ β} {C : Real} (hC : 0 <= C) :
    dist f g <= C ↔ forall x, dist (toFun f x) (toFun g x) <= C := by
  simp_rw [dist_edist, ← ENNReal.le_ofReal_iff_toReal_le (edist_ne_top _ _) hC, edist_le]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedSpace
  signature: β] : BoundedSpace (α ->ᵤ β) where
  body: by
    rw [Metric.isBounded_iff_ediam_ne_top]; rw [← lt_top_iff_ne_top]
refine lt_of_le_of_lt ?_ .ediam_ne_top.lt_top BoundedSpace.bounded_univ (α := β)
    simp only [Metric.ediam_le_iff, Set.mem_univ, edist_le, forall_const]
    exact fun f g x => Metric.edist_le_ediam_of_mem (Set.mem_univ _) (Set.mem_univ _)

中文:
实例 [有界空间
  签名: β] : 有界空间 (α ->ᵤ β) where
  定义体: by
    rw [Metric.isBounded_iff_ediam_ne_top]; rw [← lt_top_iff_ne_top]
refine lt_of_le_of_lt ?_ .ediam_ne_top.lt_top BoundedSpace.bounded_univ (α := β)
    simp only [Metric.ediam_le_iff, Set.mem_univ, edist_le, forall_const]
    exact fun f g x => Metric.edist_le_ediam_of_mem (Set.mem_univ _) (Set.mem_univ _)

Depends on / 依赖: BoundedSpace, BoundedSpace.bounded_univ, Metric, Metric.ediam_le_iff, Metric.edist_le_ediam_of_mem, Metric.isBounded_iff_ediam_ne_top, Set.mem_univ, bounded_univ, ediam_le_iff, ediam_ne_top, ediam_ne_top.lt_top, edist_le, edist_le_ediam_of_mem, forall_const, isBounded_iff_ediam_ne_top, lt_of_le_of_lt, lt_top, lt_top_iff_ne_top, mem_univ
-/
noncomputable instance [BoundedSpace β] : BoundedSpace (α ->ᵤ β) where
  bounded_univ := by
    rw [Metric.isBounded_iff_ediam_ne_top]; rw [← lt_top_iff_ne_top]
refine lt_of_le_of_lt ?_ .ediam_ne_top.lt_top BoundedSpace.bounded_univ (α := β)
    simp only [Metric.ediam_le_iff, Set.mem_univ, edist_le, forall_const]
    exact fun f g x => Metric.edist_le_ediam_of_mem (Set.mem_univ _) (Set.mem_univ _)

noncomputable instance {β : Type*} [MetricSpace β] [BoundedSpace β] : MetricSpace (α ->ᵤ β) :=
  .ofT0PseudoMetricSpace _

open BoundedContinuousFunction in
/--
lemma `isometry_ofFun_boundedContinuousFunction` / 引理 `isometry_ofFun_boundedContinuousFunction`

English:
lemma isometry_ofFun_boundedContinuousFunction
  given: [TopologicalSpace α]
  proof: by
  simp [Isometry, edist_def, edist_eq_iSup]

中文:
引理 isometry_ofFun_boundedContinuousFunction
  条件: [拓扑空间 α]
  证明: by
  simp [Isometry, edist_def, edist_eq_iSup]

Depends on / 依赖: Isometry, edist_def, edist_eq_iSup
-/
lemma isometry_ofFun_boundedContinuousFunction [TopologicalSpace α] :
    Isometry (ofFun ∘ DFunLike.coe : (α ->ᵇ β) -> α ->ᵤ β) := by
  simp [Isometry, edist_def, edist_eq_iSup]

/--
lemma `isometry_ofFun_continuousMap` / 引理 `isometry_ofFun_continuousMap`

English:
lemma isometry_ofFun_continuousMap
  given: [TopologicalSpace α] [CompactSpace α]
  proof: isometry_ofFun_boundedContinuousFunction.comp
.isometry ContinuousMap.isometryEquivBoundedOfCompact α β

中文:
引理 isometry_ofFun_continuousMap
  条件: [拓扑空间 α] [紧空间 α]
  证明: isometry_ofFun_boundedContinuousFunction.comp
.isometry ContinuousMap.isometryEquivBoundedOfCompact α β

Depends on / 依赖: ContinuousMap, ContinuousMap.isometryEquivBoundedOfCompact, isometry, isometryEquivBoundedOfCompact, isometry_ofFun_boundedContinuousFunction, isometry_ofFun_boundedContinuousFunction.comp
-/
lemma isometry_ofFun_continuousMap [TopologicalSpace α] [CompactSpace α] :
    Isometry (ofFun ∘ DFunLike.coe : C(α, β) -> α ->ᵤ β) :=
isometry_ofFun_boundedContinuousFunction.comp
.isometry ContinuousMap.isometryEquivBoundedOfCompact α β

/--
lemma `edist_continuousMapMk` / 引理 `edist_continuousMapMk`

English:
lemma edist_continuousMapMk
  statement: [TopologicalSpace α] [CompactSpace α]
  proof: by
  simp [← isometry_ofFun_continuousMap.edist_eq]

中文:
引理 edist_continuousMapMk
  结论: [拓扑空间 α] [紧空间 α]
  证明: by
  simp [← isometry_ofFun_continuousMap.edist_eq]

Depends on / 依赖: edist_eq, isometry_ofFun_continuousMap, isometry_ofFun_continuousMap.edist_eq
-/
lemma edist_continuousMapMk [TopologicalSpace α] [CompactSpace α]
    {f g : α ->ᵤ β} (hf : Continuous (toFun f)) (hg : Continuous (toFun g)) :
    edist (⟨_, hf⟩ : C(α, β)) ⟨_, hg⟩ = edist f g := by
  simp [← isometry_ofFun_continuousMap.edist_eq]

end Metric

end UniformFun

namespace UniformOnFun

variable {𝔖 𝔗 : Set (Set α)}

section EMetric

variable [PseudoEMetricSpace β]

/--
lemma `continuous_of_forall_lipschitzWith` / 引理 `continuous_of_forall_lipschitzWith`

English:
lemma continuous_of_forall_lipschitzWith
  statement: {f : γ -> α ->ᵤ[𝔖] β} (K : Set α -> Real>=0)
  proof: by
  rw [UniformOnFun.continuous_rng_iff]
  refine fun s hs => LipschitzWith.continuous (K := K s) ?_
  rw [UniformFun.lipschitzWith_iff]
  rintro ⟨y, hy⟩
  exact h s hs y hy

@[nolint unusedArguments]

中文:
引理 continuous_of_对任意_lipschitzWith
  结论: {f : γ -> α ->ᵤ[𝔖] β} (K : 集合 α -> 实数>=0)
  证明: by
  rw [UniformOnFun.continuous_rng_iff]
  refine fun s hs => LipschitzWith.continuous (K := K s) ?_
  rw [UniformFun.lipschitzWith_iff]
  rintro ⟨y, hy⟩
  exact h s hs y hy

@[nolint unusedArguments]

Depends on / 依赖: LipschitzWith, LipschitzWith.continuous, UniformFun, UniformFun.lipschitzWith_iff, UniformOnFun, UniformOnFun.continuous_rng_iff, continuous, continuous_rng_iff, lipschitzWith_iff
-/
lemma continuous_of_forall_lipschitzWith {f : γ -> α ->ᵤ[𝔖] β} (K : Set α -> Real>=0)
    (h : forall s in 𝔖, forall c in s, LipschitzWith (K s) (fun x => toFun 𝔖 (f x) c)) :
    Continuous f := by
  rw [UniformOnFun.continuous_rng_iff]
  refine fun s hs => LipschitzWith.continuous (K := K s) ?_
  rw [UniformFun.lipschitzWith_iff]
  rintro ⟨y, hy⟩
  exact h s hs y hy

@[nolint unusedArguments]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: 𝔖] : EDist (α ->ᵤ[𝔖] β) where
  body: ⨆ x in ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x)

中文:
实例 [有限
  签名: 𝔖] : EDist (α ->ᵤ[𝔖] β) where
  定义体: ⨆ x in ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x)
-/
noncomputable instance [Finite 𝔖] : EDist (α ->ᵤ[𝔖] β) where
  edist f g := ⨆ x in ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x)

/--
lemma `edist_def` / 引理 `edist_def`

English:
lemma edist_def
  given: [Finite 𝔖] (f g : α ->ᵤ[𝔖] β)
  proof: rfl

中文:
引理 edist_def
  条件: [有限 𝔖] (f g : α ->ᵤ[𝔖] β)
  证明: rfl
-/
lemma edist_def [Finite 𝔖] (f g : α ->ᵤ[𝔖] β) :
    edist f g = ⨆ x in ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) :=
  rfl

/--
lemma `edist_def'` / 引理 `edist_def'`

English:
lemma edist_def'
  given: [Finite 𝔖] (f g : α ->ᵤ[𝔖] β)
  proof: by
  simp [edist_def, iSup_and, iSup_comm (ι := α)]

中文:
引理 edist_def'
  条件: [有限 𝔖] (f g : α ->ᵤ[𝔖] β)
  证明: by
  simp [edist_def, iSup_and, iSup_comm (ι := α)]

Depends on / 依赖: edist_def, iSup_and, iSup_comm
-/
lemma edist_def' [Finite 𝔖] (f g : α ->ᵤ[𝔖] β) :
    edist f g = ⨆ s in 𝔖, ⨆ x in s, edist (toFun 𝔖 f x) (toFun 𝔖 g x) := by
  simp [edist_def, iSup_and, iSup_comm (ι := α)]

/--
lemma `edist_eq_restrict_sUnion` / 引理 `edist_eq_restrict_sUnion`

English:
lemma edist_eq_restrict_sUnion
  given: [Finite 𝔖] {f g : α ->ᵤ[𝔖] β}
  proof: iSup_subtype'

中文:
引理 edist_eq_restrict_sUnion
  条件: [有限 𝔖] {f g : α ->ᵤ[𝔖] β}
  证明: iSup_subtype'

Depends on / 依赖: iSup_subtype
-/
lemma edist_eq_restrict_sUnion [Finite 𝔖] {f g : α ->ᵤ[𝔖] β} :
    edist f g = edist
      (UniformFun.ofFun ((⋃₀ 𝔖).domRestrict (toFun 𝔖 f)))
      (UniformFun.ofFun ((⋃₀ 𝔖).domRestrict (toFun 𝔖 g))) :=
  iSup_subtype'

/--
lemma `edist_eq_pi_restrict` / 引理 `edist_eq_pi_restrict`

English:
lemma edist_eq_pi_restrict
  given: [Fintype 𝔖] {f g : α ->ᵤ[𝔖] β}
  proof: by
  simp_rw [edist_def', iSup_subtype', edist_pi_def, Finset.sup_univ_eq_iSup]
  rfl

中文:
引理 edist_eq_pi_restrict
  条件: [有限类型 𝔖] {f g : α ->ᵤ[𝔖] β}
  证明: by
  simp_rw [edist_def', iSup_subtype', edist_pi_def, Finset.sup_univ_eq_iSup]
  rfl

Depends on / 依赖: Finset, Finset.sup_univ_eq_iSup, edist_def, edist_pi_def, iSup_subtype, simp_rw, sup_univ_eq_iSup
-/
lemma edist_eq_pi_restrict [Fintype 𝔖] {f g : α ->ᵤ[𝔖] β} :
    edist f g = edist
      (fun s : 𝔖 => UniformFun.ofFun ((s : Set α).domRestrict (toFun 𝔖 f)))
      (fun s : 𝔖 => UniformFun.ofFun ((s : Set α).domRestrict (toFun 𝔖 g))) := by
  simp_rw [edist_def', iSup_subtype', edist_pi_def, Finset.sup_univ_eq_iSup]
  rfl

variable [Finite 𝔖]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoEMetricSpace (α ->ᵤ[𝔖] β)
  body: by simp [edist_eq_restrict_sUnion]
  edist_comm := by simp [edist_eq_restrict_sUnion, edist_comm]
  edist_triangle f₁ f₂ f₃ := by simp [edist_eq_restrict_sUnion, edist_triangle]
  toUniformSpace := inferInstance
  uniformity_edist := by
    let _ := Fintype.ofFinite 𝔖;
    simp_rw [← isUniformInducing_pi_restrict.comap_uniformity,
      PseudoEMetricSpace.uniformity_edist, comap_iInf, comap_principal, edist_eq_pi_restrict,
      Set.preimage_ofPred_eq]

中文:
实例 :
  签名: PseudoEMetric空间 (α ->ᵤ[𝔖] β)
  定义体: by simp [edist_eq_restrict_sUnion]
  edist_comm := by simp [edist_eq_restrict_sUnion, edist_comm]
  edist_triangle f₁ f₂ f₃ := by simp [edist_eq_restrict_sUnion, edist_triangle]
  toUniformSpace := inferInstance
  uniformity_edist := by
    let _ := Fintype.ofFinite 𝔖;
    simp_rw [← isUniformInducing_pi_restrict.comap_uniformity,
      PseudoEMetricSpace.uniformity_edist, comap_iInf, comap_principal, edist_eq_pi_restrict,
      Set.preimage_ofPred_eq]

Depends on / 依赖: Fintype, Fintype.ofFinite, PseudoEMetricSpace, PseudoEMetricSpace.uniformity_edist, Set.preimage_ofPred_eq, comap_iInf, comap_principal, comap_uniformity, edist_comm, edist_eq_pi_restrict, edist_eq_restrict_sUnion, edist_triangle, isUniformInducing_pi_restrict, isUniformInducing_pi_restrict.comap_uniformity, ofFinite, preimage_ofPred_eq, simp_rw, toUniformSpace, uniformity_edist
-/
noncomputable instance : PseudoEMetricSpace (α ->ᵤ[𝔖] β) where
  edist_self f := by simp [edist_eq_restrict_sUnion]
  edist_comm := by simp [edist_eq_restrict_sUnion, edist_comm]
  edist_triangle f₁ f₂ f₃ := by simp [edist_eq_restrict_sUnion, edist_triangle]
  toUniformSpace := inferInstance
  uniformity_edist := by
    let _ := Fintype.ofFinite 𝔖;
    simp_rw [← isUniformInducing_pi_restrict.comap_uniformity,
      PseudoEMetricSpace.uniformity_edist, comap_iInf, comap_principal, edist_eq_pi_restrict,
      Set.preimage_ofPred_eq]

/--
lemma `edist_le` / 引理 `edist_le`

English:
lemma edist_le
  given: {f g : α ->ᵤ[𝔖] β} {C : Real>=0∞}
  proof: by
  simp_rw [edist_def, iSup₂_le_iff]

中文:
引理 edist_le
  条件: {f g : α ->ᵤ[𝔖] β} {C : 实数>=0∞}
  证明: by
  simp_rw [edist_def, iSup₂_le_iff]

Depends on / 依赖: edist_def, simp_rw
-/
lemma edist_le {f g : α ->ᵤ[𝔖] β} {C : Real>=0∞} :
    edist f g <= C ↔ forall x in ⋃₀ 𝔖, edist (toFun 𝔖 f x) (toFun 𝔖 g x) <= C := by
  simp_rw [edist_def, iSup₂_le_iff]

/--
lemma `lipschitzWith_iff` / 引理 `lipschitzWith_iff`

English:
lemma lipschitzWith_iff
  given: {f : γ -> α ->ᵤ[𝔖] β} {K : Real>=0}
  proof: by
  simp [LipschitzWith, edist_le]
  tauto

中文:
引理 lipschitzWith_iff
  条件: {f : γ -> α ->ᵤ[𝔖] β} {K : 实数>=0}
  证明: by
  simp [LipschitzWith, edist_le]
  tauto

Depends on / 依赖: LipschitzWith, edist_le
-/
lemma lipschitzWith_iff {f : γ -> α ->ᵤ[𝔖] β} {K : Real>=0} :
    LipschitzWith K f ↔ forall c in ⋃₀ 𝔖, LipschitzWith K (fun x => toFun 𝔖 (f x) c) := by
  simp [LipschitzWith, edist_le]
  tauto

/--
lemma `lipschitzOnWith_iff` / 引理 `lipschitzOnWith_iff`

English:
lemma lipschitzOnWith_iff
  given: {f : γ -> α ->ᵤ[𝔖] β} {K : Real>=0} {s : Set γ}
  proof: by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

中文:
引理 lipschitzOnWith_iff
  条件: {f : γ -> α ->ᵤ[𝔖] β} {K : 实数>=0} {s : 集合 γ}
  证明: by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

Depends on / 依赖: lipschitzOnWith_iff_restrict, lipschitzWith_iff
-/
lemma lipschitzOnWith_iff {f : γ -> α ->ᵤ[𝔖] β} {K : Real>=0} {s : Set γ} :
    LipschitzOnWith K f s ↔ forall c in ⋃₀ 𝔖, LipschitzOnWith K (fun x => toFun 𝔖 (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

/--
lemma `edist_eval_le` / 引理 `edist_eval_le`

English:
lemma edist_eval_le
  given: {f g : α ->ᵤ[𝔖] β} {x : α} (hx : x in ⋃₀ 𝔖)
  proof: edist_le.mp le_rfl x hx

中文:
引理 edist_eval_le
  条件: {f g : α ->ᵤ[𝔖] β} {x : α} (hx : x in ⋃₀ 𝔖)
  证明: edist_le.mp le_rfl x hx

Depends on / 依赖: edist_le, edist_le.mp, le_rfl
-/
lemma edist_eval_le {f g : α ->ᵤ[𝔖] β} {x : α} (hx : x in ⋃₀ 𝔖) :
    edist (toFun 𝔖 f x) (toFun 𝔖 g x) <= edist f g :=
  edist_le.mp le_rfl x hx

/--
lemma `lipschitzWith_eval` / 引理 `lipschitzWith_eval`

English:
lemma lipschitzWith_eval
  given: {x : α} (hx : x in ⋃₀ 𝔖)
  proof: by
  intro f g
  simpa only [ENNReal.coe_one, one_mul] using edist_eval_le hx

中文:
引理 lipschitzWith_eval
  条件: {x : α} (hx : x in ⋃₀ 𝔖)
  证明: by
  intro f g
  simpa only [ENNReal.coe_one, one_mul] using edist_eval_le hx

Depends on / 依赖: ENNReal, ENNReal.coe_one, coe_one, edist_eval_le, one_mul
-/
lemma lipschitzWith_eval {x : α} (hx : x in ⋃₀ 𝔖) :
    LipschitzWith 1 (fun f : α ->ᵤ[𝔖] β => toFun 𝔖 f x) := by
  intro f g
  simpa only [ENNReal.coe_one, one_mul] using edist_eval_le hx

/--
lemma `lipschitzWith_one_ofFun_toFun` / 引理 `lipschitzWith_one_ofFun_toFun`

English:
lemma lipschitzWith_one_ofFun_toFun
  proof: lipschitzWith_iff.mpr fun _ _ => UniformFun.lipschitzWith_eval _

中文:
引理 lipschitzWith_one_ofFun_toFun
  证明: lipschitzWith_iff.mpr fun _ _ => UniformFun.lipschitzWith_eval _

Depends on / 依赖: UniformFun, UniformFun.lipschitzWith_eval, lipschitzWith_eval, lipschitzWith_iff, lipschitzWith_iff.mpr
-/
lemma lipschitzWith_one_ofFun_toFun :
    LipschitzWith 1 (ofFun 𝔖 ∘ UniformFun.toFun : (α ->ᵤ β) -> (α ->ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun _ _ => UniformFun.lipschitzWith_eval _

/--
lemma `lipschitzWith_one_ofFun_toFun'` / 引理 `lipschitzWith_one_ofFun_toFun'`

English:
lemma lipschitzWith_one_ofFun_toFun'
  given: [Finite 𝔗] (h : ⋃₀ 𝔖 subseteq ⋃₀ 𝔗)
  proof: lipschitzWith_iff.mpr fun _x hx => lipschitzWith_eval (h hx)

中文:
引理 lipschitzWith_one_ofFun_toFun'
  条件: [有限 𝔗] (h : ⋃₀ 𝔖 subseteq ⋃₀ 𝔗)
  证明: lipschitzWith_iff.mpr fun _x hx => lipschitzWith_eval (h hx)

Depends on / 依赖: lipschitzWith_eval, lipschitzWith_iff, lipschitzWith_iff.mpr
-/
lemma lipschitzWith_one_ofFun_toFun' [Finite 𝔗] (h : ⋃₀ 𝔖 subseteq ⋃₀ 𝔗) :
    LipschitzWith 1 (ofFun 𝔖 ∘ toFun 𝔗 : (α ->ᵤ[𝔗] β) -> (α ->ᵤ[𝔖] β)) :=
  lipschitzWith_iff.mpr fun _x hx => lipschitzWith_eval (h hx)

/--
lemma `lipschitzWith_restrict` / 引理 `lipschitzWith_restrict`

English:
lemma lipschitzWith_restrict
  given: (s : Set α) (hs : s in 𝔖)
  proof: UniformFun.lipschitzWith_iff.mpr fun x => lipschitzWith_eval ⟨s, hs, x.2⟩

中文:
引理 lipschitzWith_restrict
  条件: (s : 集合 α) (hs : s in 𝔖)
  证明: UniformFun.lipschitzWith_iff.mpr fun x => lipschitzWith_eval ⟨s, hs, x.2⟩

Depends on / 依赖: UniformFun, UniformFun.lipschitzWith_iff.mpr, lipschitzWith_eval, lipschitzWith_iff
-/
lemma lipschitzWith_restrict (s : Set α) (hs : s in 𝔖) :
    LipschitzWith 1 (UniformFun.ofFun ∘ s.domRestrict ∘ toFun 𝔖 : (α ->ᵤ[𝔖] β) -> (s ->ᵤ β)) :=
  UniformFun.lipschitzWith_iff.mpr fun x => lipschitzWith_eval ⟨s, hs, x.2⟩

/--
lemma `isometry_restrict` / 引理 `isometry_restrict`

English:
lemma isometry_restrict
  given: (s : Set α)
  proof: by
  simp [Isometry, edist_def, UniformFun.edist_def, iSup_subtype]

中文:
引理 isometry_restrict
  条件: (s : 集合 α)
  证明: by
  simp [Isometry, edist_def, UniformFun.edist_def, iSup_subtype]

Depends on / 依赖: Isometry, UniformFun, UniformFun.edist_def, edist_def, iSup_subtype
-/
lemma isometry_restrict (s : Set α) :
    Isometry (UniformFun.ofFun ∘ s.domRestrict ∘ toFun {s} : (α ->ᵤ[{s}] β) -> (s ->ᵤ β)) := by
  simp [Isometry, edist_def, UniformFun.edist_def, iSup_subtype]

end EMetric

section Metric

variable [Finite 𝔖] [PseudoMetricSpace β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedSpace
  signature: β] : PseudoMetricSpace (α ->ᵤ[𝔖] β)
  body: PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g => ⨆ x : ⋃₀ 𝔖, dist (toFun 𝔖 f x) (toFun 𝔖 g x))
    (fun _ _ => Real.iSup_nonneg fun i => dist_nonneg)
    fun f g => by
      cases isEmpty_or_nonempty (⋃₀ 𝔖)
      · simp_all [edist_def]
      have : BddAbove (.range fun x : ⋃₀ 𝔖 => dist (toFun 𝔖 f x) (toFun 𝔖 g x)) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      refine ENNReal.eq_of_forall_le_nnreal_iff fun r => ?_
      simp [edist_def, ciSup_le_iff this]

中文:
实例 [有界空间
  签名: β] : 伪度量空间 (α ->ᵤ[𝔖] β)
  定义体: PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g => ⨆ x : ⋃₀ 𝔖, dist (toFun 𝔖 f x) (toFun 𝔖 g x))
    (fun _ _ => Real.iSup_nonneg fun i => dist_nonneg)
    fun f g => by
      cases isEmpty_or_nonempty (⋃₀ 𝔖)
      · simp_all [edist_def]
      have : BddAbove (.range fun x : ⋃₀ 𝔖 => dist (toFun 𝔖 f x) (toFun 𝔖 g x)) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      refine ENNReal.eq_of_forall_le_nnreal_iff fun r => ?_
      simp [edist_def, ciSup_le_iff this]

Depends on / 依赖: BddAbove, BoundedSpace, BoundedSpace.bounded_univ.ediam_ne_top, ENNReal, ENNReal.ofReal_le_iff_le_toReal, Metric, Metric.ediam, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, Real.iSup_nonneg, bounded_univ, contextual, dist_nonneg, ediam_ne_top, edist_def, edist_dist, eq_comm, iSup_nonneg, isEmpty_or_nonempty, mem_upperBounds
-/
noncomputable instance [BoundedSpace β] : PseudoMetricSpace (α ->ᵤ[𝔖] β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g => ⨆ x : ⋃₀ 𝔖, dist (toFun 𝔖 f x) (toFun 𝔖 g x))
    (fun _ _ => Real.iSup_nonneg fun i => dist_nonneg)
    fun f g => by
      cases isEmpty_or_nonempty (⋃₀ 𝔖)
      · simp_all [edist_def]
      have : BddAbove (.range fun x : ⋃₀ 𝔖 => dist (toFun 𝔖 f x) (toFun 𝔖 g x)) := by
        use (Metric.ediam (.univ : Set β)).toReal
        simp +contextual [mem_upperBounds, eq_comm (a := dist _ _), ← edist_dist,
          ← ENNReal.ofReal_le_iff_le_toReal BoundedSpace.bounded_univ.ediam_ne_top,
          Metric.edist_le_ediam_of_mem]
      refine ENNReal.eq_of_forall_le_nnreal_iff fun r => ?_
      simp [edist_def, ciSup_le_iff this]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedSpace
  signature: β] : BoundedSpace (α ->ᵤ[𝔖] β) where
  body: by
.isBounded_image (.all Set.univ) convert! lipschitzWith_one_ofFun_toFun (𝔖 := 𝔖) (β := β)
    ext f
    simp only [Set.mem_univ, Function.comp_apply, Set.image_univ, Set.mem_range, true_iff]
    exact ⟨UniformFun.ofFun (toFun 𝔖 f), by simp⟩

中文:
实例 [有界空间
  签名: β] : 有界空间 (α ->ᵤ[𝔖] β) where
  定义体: by
.isBounded_image (.all Set.univ) convert! lipschitzWith_one_ofFun_toFun (𝔖 := 𝔖) (β := β)
    ext f
    simp only [Set.mem_univ, Function.comp_apply, Set.image_univ, Set.mem_range, true_iff]
    exact ⟨UniformFun.ofFun (toFun 𝔖 f), by simp⟩

Depends on / 依赖: Function, Function.comp_apply, Set.image_univ, Set.mem_range, Set.mem_univ, Set.univ, UniformFun, UniformFun.ofFun, comp_apply, convert, image_univ, isBounded_image, lipschitzWith_one_ofFun_toFun, mem_range, mem_univ, true_iff
-/
noncomputable instance [BoundedSpace β] : BoundedSpace (α ->ᵤ[𝔖] β) where
  bounded_univ := by
.isBounded_image (.all Set.univ) convert! lipschitzWith_one_ofFun_toFun (𝔖 := 𝔖) (β := β)
    ext f
    simp only [Set.mem_univ, Function.comp_apply, Set.image_univ, Set.mem_range, true_iff]
    exact ⟨UniformFun.ofFun (toFun 𝔖 f), by simp⟩

/--
lemma `edist_continuousRestrict` / 引理 `edist_continuousRestrict`

English:
lemma edist_continuousRestrict
  statement: [TopologicalSpace α] {f g : α ->ᵤ[𝔖] β}
  proof: by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

中文:
引理 edist_continuousRestrict
  结论: [拓扑空间 α] {f g : α ->ᵤ[𝔖] β}
  证明: by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

Depends on / 依赖: ContinuousMap, ContinuousMap.edist_eq_iSup, edist_def, edist_eq_iSup, iSup_subtype
-/
lemma edist_continuousRestrict [TopologicalSpace α] {f g : α ->ᵤ[𝔖] β}
    [CompactSpace (⋃₀ 𝔖)] (hf : ContinuousOn (toFun 𝔖 f) (⋃₀ 𝔖))
    (hg : ContinuousOn (toFun 𝔖 g) (⋃₀ 𝔖)) :
    edist (⟨_, hf.domRestrict⟩ : C(⋃₀ 𝔖, β)) ⟨_, hg.domRestrict⟩ = edist f g := by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

/--
lemma `edist_continuousRestrict_of_singleton` / 引理 `edist_continuousRestrict_of_singleton`

English:
lemma edist_continuousRestrict_of_singleton
  statement: [TopologicalSpace α] {s : Set α}
  proof: by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

中文:
引理 edist_continuousRestrict_of_singleton
  结论: [拓扑空间 α] {s : 集合 α}
  证明: by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

Depends on / 依赖: ContinuousMap, ContinuousMap.edist_eq_iSup, edist_def, edist_eq_iSup, iSup_subtype
-/
lemma edist_continuousRestrict_of_singleton [TopologicalSpace α] {s : Set α}
    {f g : α ->ᵤ[{s}] β} [CompactSpace s] (hf : ContinuousOn (toFun {s} f) s)
    (hg : ContinuousOn (toFun {s} g) s) :
    edist (⟨_, hf.domRestrict⟩ : C(s, β)) ⟨_, hg.domRestrict⟩ = edist f g := by
  simp [ContinuousMap.edist_eq_iSup, iSup_subtype, edist_def]

end Metric

end UniformOnFun
