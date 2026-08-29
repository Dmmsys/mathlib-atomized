/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# The completion of a metric space

Completion of uniform spaces are already defined in `Topology.UniformSpace.Completion`. We show
here that the uniform space completion of a metric space inherits a metric space structure,
by extending the distance to the completion and checking that it is indeed a distance, and that
it defines the same uniformity as the already defined uniform structure on the completion
-/

@[expose] public section

open Set Filter UniformSpace Metric

open Filter Topology Uniformity

noncomputable section

universe u v

variable {α : Type u} {β : Type v} [PseudoMetricSpace α]

namespace UniformSpace.Completion

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist (Completion α)
  body: ⟨Completion.extension₂ dist⟩

中文:
实例 :
  签名: Dist (完备化 α)
  定义体: ⟨Completion.extension₂ dist⟩

Depends on / 依赖: Completion, Completion.extension
-/
instance : Dist (Completion α) :=
  ⟨Completion.extension₂ dist⟩

/--
theorem `uniformContinuous_dist` / 定理 `uniformContinuous_dist`

English:
theorem uniformContinuous_dist
  proof: uniformContinuous_extension₂ dist

中文:
定理 uniformContinuous_dist
  证明: uniformContinuous_extension₂ dist
-/
protected theorem uniformContinuous_dist :
    UniformContinuous fun p : Completion α × Completion α => dist p.1 p.2 :=
  uniformContinuous_extension₂ dist

/--
theorem `continuous_dist` / 定理 `continuous_dist`

English:
theorem continuous_dist
  statement: [TopologicalSpace β] {f g : β -> Completion α} (hf : Continuous f)
  proof: Completion.uniformContinuous_dist.continuous.comp (hf.prodMk hg :)

中文:
定理 continuous_dist
  结论: [拓扑空间 β] {f g : β -> 完备化 α} (hf : 连续 f)
  证明: Completion.uniformContinuous_dist.continuous.comp (hf.prodMk hg :)
-/
protected theorem continuous_dist [TopologicalSpace β] {f g : β -> Completion α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => dist (f x) (g x) :=
  Completion.uniformContinuous_dist.continuous.comp (hf.prodMk hg :)

/-- The new distance is an extension of the original distance. -/
@[simp]
/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  given: (x y : α)
  statement: dist (x : Completion α) y = dist x y
  proof: Completion.extension₂_coe_coe uniformContinuous_dist _ _

中文:
定理 dist_eq
  条件: (x y : α)
  结论: dist (x : 完备化 α) y = dist x y
  证明: Completion.extension₂_coe_coe uniformContinuous_dist _ _
-/
protected theorem dist_eq (x y : α) : dist (x : Completion α) y = dist x y :=
  Completion.extension₂_coe_coe uniformContinuous_dist _ _


/--
theorem `dist_self` / 定理 `dist_self`

English:
theorem dist_self
  given: (x : Completion α)
  statement: dist x x = 0
  proof: by
  refine induction_on x ?_ ?_
  · refine isClosed_eq ?_ continuous_const
    exact Completion.continuous_dist continuous_id continuous_id
  · intro a
    rw [Completion.dist_eq]; rw [dist_self]

中文:
定理 dist_self
  条件: (x : 完备化 α)
  结论: dist x x = 0
  证明: by
  refine induction_on x ?_ ?_
  · refine isClosed_eq ?_ continuous_const
    exact Completion.continuous_dist continuous_id continuous_id
  · intro a
    rw [Completion.dist_eq]; rw [dist_self]
-/
protected theorem dist_self (x : Completion α) : dist x x = 0 := by
  refine induction_on x ?_ ?_
  · refine isClosed_eq ?_ continuous_const
    exact Completion.continuous_dist continuous_id continuous_id
  · intro a
    rw [Completion.dist_eq]; rw [dist_self]

/--
theorem `dist_comm` / 定理 `dist_comm`

English:
theorem dist_comm
  given: (x y : Completion α)
  statement: dist x y = dist y x
  proof: by
  refine induction_on₂ x y ?_ ?_
  · exact isClosed_eq (Completion.continuous_dist continuous_fst continuous_snd)
        (Completion.continuous_dist continuous_snd continuous_fst)
  · intro a b
    rw [Completion.dist_eq]; rw [Completion.dist_eq]; rw [dist_comm]

中文:
定理 dist_comm
  条件: (x y : 完备化 α)
  结论: dist x y = dist y x
  证明: by
  refine induction_on₂ x y ?_ ?_
  · exact isClosed_eq (Completion.continuous_dist continuous_fst continuous_snd)
        (Completion.continuous_dist continuous_snd continuous_fst)
  · intro a b
    rw [Completion.dist_eq]; rw [Completion.dist_eq]; rw [dist_comm]
-/
protected theorem dist_comm (x y : Completion α) : dist x y = dist y x := by
  refine induction_on₂ x y ?_ ?_
  · exact isClosed_eq (Completion.continuous_dist continuous_fst continuous_snd)
        (Completion.continuous_dist continuous_snd continuous_fst)
  · intro a b
    rw [Completion.dist_eq]; rw [Completion.dist_eq]; rw [dist_comm]

/--
theorem `dist_triangle` / 定理 `dist_triangle`

English:
theorem dist_triangle
  given: (x y z : Completion α)
  statement: dist x z <= dist x y + dist y z
  proof: by
  refine induction_on₃ x y z ?_ ?_
  · refine isClosed_le ?_ (Continuous.add ?_ ?_) <;>
      apply_rules [Completion.continuous_dist, Continuous.fst, Continuous.snd, continuous_id]
  · intro a b c
    rw [Completion.dist_eq]; rw [Completion.dist_eq]; rw [Completion.dist_eq]
    exact dist_triang

中文:
定理 dist_triangle
  条件: (x y z : 完备化 α)
  结论: dist x z <= dist x y + dist y z
  证明: by
  refine induction_on₃ x y z ?_ ?_
  · refine isClosed_le ?_ (Continuous.add ?_ ?_) <;>
      apply_rules [Completion.continuous_dist, Continuous.fst, Continuous.snd, continuous_id]
  · intro a b c
    rw [Completion.dist_eq]; rw [Completion.dist_eq]; rw [Completion.dist_eq]
    exact dist_triang
-/
protected theorem dist_triangle (x y z : Completion α) : dist x z <= dist x y + dist y z := by
  refine induction_on₃ x y z ?_ ?_
  · refine isClosed_le ?_ (Continuous.add ?_ ?_) <;>
      apply_rules [Completion.continuous_dist, Continuous.fst, Continuous.snd, continuous_id]
  · intro a b c
    rw [Completion.dist_eq]; rw [Completion.dist_eq]; rw [Completion.dist_eq]
    exact dist_triangle a b c

/--
theorem `mem_uniformity_dist` / 定理 `mem_uniformity_dist`

English:
theorem mem_uniformity_dist
  given: (s : Set (Completion α × Completion α))
  proof: by
  constructor
  · /- Start from an entourage `s`. It contains a closed entourage `t`. Its pullback in `α` is an
      entourage, so it contains an `ε`-neighborhood of the diagonal by definition of the entourages
      in metric spaces. Then `t` contains an `ε`-neighborhood of the diagonal in `Com

中文:
定理 mem_uniformity_dist
  条件: (s : 集合 (完备化 α × 完备化 α))
  证明: by
  constructor
  · /- Start from an entourage `s`. It contains a closed entourage `t`. Its pullback in `α` is an
      entourage, so it contains an `ε`-neighborhood of the diagonal by definition of the entourages
      in metric spaces. Then `t` contains an `ε`-neighborhood of the diagonal in `Com
-/
protected theorem mem_uniformity_dist (s : Set (Completion α × Completion α)) :
    s in 𝓤 (Completion α) ↔ exists ε > 0, forall {a b}, dist a b < ε -> (a, b) in s := by
  constructor
  · /- Start from an entourage `s`. It contains a closed entourage `t`. Its pullback in `α` is an
      entourage, so it contains an `ε`-neighborhood of the diagonal by definition of the entourages
      in metric spaces. Then `t` contains an `ε`-neighborhood of the diagonal in `Completion α`, as
      closed properties pass to the completion. -/
    intro hs
    rcases mem_uniformity_isClosed hs with ⟨t, ht, ⟨tclosed, ts⟩⟩
    have A : { x : α × α | (↑x.1, ↑x.2) in t } in uniformity α :=
      uniformContinuous_def.1 (uniformContinuous_coe α) t ht
    rcases mem_uniformity_dist.1 A with ⟨ε, εpos, hε⟩
    refine ⟨ε, εpos, @fun x y hxy => ?_⟩
    have : ε <= dist x y ∨ (x, y) in t := by
      refine induction_on₂ x y ?_ ?_
      · have : { x : Completion α × Completion α | ε <= dist x.fst x.snd ∨ (x.fst, x.snd) in t } =
               { p : Completion α × Completion α | ε <= dist p.1 p.2 } union t := by ext; simp
        rw [this]
        apply IsClosed.union _ tclosed
        exact isClosed_le continuous_const Completion.uniformContinuous_dist.continuous
      · intro x y
        rw [Completion.dist_eq]
        by_cases! h : ε <= dist x y
        · exact Or.inl h
        · have Z := hε h
          simp only [Set.mem_ofPred_eq] at Z
          exact Or.inr Z
    simp only [not_le.mpr hxy, false_or] at this
    exact ts this
  · /- Start from a set `s` containing an ε-neighborhood of the diagonal in `Completion α`. To show
        that it is an entourage, we use the fact that `dist` is uniformly continuous on
        `Completion α × Completion α` (this is a general property of the extension of uniformly
        continuous functions). Therefore, the preimage of the ε-neighborhood of the diagonal in ℝ
        is an entourage in `Completion α × Completion α`. Massaging this property, it follows that
        the ε-neighborhood of the diagonal is an entourage in `Completion α`, and therefore this is
        also the case of `s`. -/
    rintro ⟨ε, εpos, hε⟩
    let r : Set (Real × Real) := { p | dist p.1 p.2 < ε }
    have : r in uniformity Real := Metric.dist_mem_uniformity εpos
    have T := uniformContinuous_def.1 (@Completion.uniformContinuous_dist α _) r this
    simp only [uniformity_prod_eq_prod, mem_prod_iff, Filter.mem_map] at T
    rcases T with ⟨t1, ht1, t2, ht2, ht⟩
    refine mem_of_superset ht1 ?_
    have A : forall a b : Completion α, (a, b) in t1 -> dist a b < ε := by
      intro a b hab
      have : ((a, b), (a, a)) in t1 ×ˢ t2 := ⟨hab, refl_mem_uniformity ht2⟩
      exact lt_of_le_of_lt (le_abs_self _)
        (by simpa [r, Completion.dist_self, Real.dist_eq, Completion.dist_comm] using ht this)
    grind

/--
theorem `uniformity_dist'` / 定理 `uniformity_dist'`

English:
theorem uniformity_dist'
  proof: by
  ext s; rw [mem_iInf_of_directed]
  · simp [Completion.mem_uniformity_dist, subset_def]
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    use ⟨min r p, lt_min hr hp⟩
    simp +contextual

中文:
定理 uniformity_dist'
  证明: by
  ext s; rw [mem_iInf_of_directed]
  · simp [Completion.mem_uniformity_dist, subset_def]
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    use ⟨min r p, lt_min hr hp⟩
    simp +contextual
-/
protected theorem uniformity_dist' :
    𝓤 (Completion α) = ⨅ ε : { ε : Real // 0 < ε }, 𝓟 { p | dist p.1 p.2 < ε.val } := by
  ext s; rw [mem_iInf_of_directed]
  · simp [Completion.mem_uniformity_dist, subset_def]
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    use ⟨min r p, lt_min hr hp⟩
    simp +contextual

/--
theorem `uniformity_dist` / 定理 `uniformity_dist`

English:
theorem uniformity_dist
  statement: 𝓤 (Completion α) = ⨅ ε > 0, 𝓟 { p | dist p.1 p.2 < ε }
  proof: by
  simpa [iInf_subtype] using @Completion.uniformity_dist' α _

中文:
定理 uniformity_dist
  结论: 𝓤 (完备化 α) = ⨅ ε > 0, 𝓟 { p | dist p.1 p.2 < ε }
  证明: by
  simpa [iInf_subtype] using @Completion.uniformity_dist' α _
-/
protected theorem uniformity_dist : 𝓤 (Completion α) = ⨅ ε > 0, 𝓟 { p | dist p.1 p.2 < ε } := by
  simpa [iInf_subtype] using @Completion.uniformity_dist' α _

/--
Instance `instMetricSpace` / 实例 `instMetricSpace`

English:
instance instMetricSpace
  signature: : MetricSpace (Completion α)
  body: @MetricSpace.ofT0PseudoMetricSpace _
    { dist_self := Completion.dist_self
      dist_comm := Completion.dist_comm
      dist_triangle := Completion.dist_triangle
      dist := dist
      toUniformSpace := inferInstance
      uniformity_dist := Completion.uniformity_dist } _

中文:
实例 instMetricSpace
  签名: : 度量空间 (完备化 α)
  定义体: @MetricSpace.ofT0PseudoMetricSpace _
    { dist_self := Completion.dist_self
      dist_comm := Completion.dist_comm
      dist_triangle := Completion.dist_triangle
      dist := dist
      toUniformSpace := inferInstance
      uniformity_dist := Completion.uniformity_dist } _

Depends on / 依赖: Completion, Completion.dist_comm, Completion.dist_self, Completion.dist_triangle, Completion.uniformity_dist, MetricSpace, MetricSpace.ofT0PseudoMetricSpace, dist_comm, dist_self, dist_triangle, ofT0PseudoMetricSpace, toUniformSpace, uniformity_dist
-/
instance instMetricSpace : MetricSpace (Completion α) :=
  @MetricSpace.ofT0PseudoMetricSpace _
    { dist_self := Completion.dist_self
      dist_comm := Completion.dist_comm
      dist_triangle := Completion.dist_triangle
      dist := dist
      toUniformSpace := inferInstance
      uniformity_dist := Completion.uniformity_dist } _

/--
theorem `coe_isometry` / 定理 `coe_isometry`

English:
theorem coe_isometry
  statement: Isometry ((↑) : α -> Completion α)
  proof: Isometry.of_dist_eq Completion.dist_eq

@[simp]

中文:
定理 coe_isometry
  结论: 等距 ((↑) : α -> 完备化 α)
  证明: Isometry.of_dist_eq Completion.dist_eq

@[simp]

Depends on / 依赖: Completion, Completion.dist_eq, Isometry, Isometry.of_dist_eq, dist_eq, of_dist_eq
-/
theorem coe_isometry : Isometry ((↑) : α -> Completion α) :=
  Isometry.of_dist_eq Completion.dist_eq

@[simp]
/--
theorem `edist_eq` / 定理 `edist_eq`

English:
theorem edist_eq
  given: (x y : α)
  statement: edist (x : Completion α) y = edist x y
  proof: coe_isometry x y

中文:
定理 edist_eq
  条件: (x y : α)
  结论: edist (x : 完备化 α) y = edist x y
  证明: coe_isometry x y
-/
protected theorem edist_eq (x y : α) : edist (x : Completion α) y = edist x y :=
  coe_isometry x y

instance {M} [Zero M] [Zero α] [SMul M α] [PseudoMetricSpace M] [IsBoundedSMul M α] :
    IsBoundedSMul M (Completion α) where
  dist_smul_pair' c x₁ x₂ := by
    induction x₁, x₂ using induction_on₂ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x₁ x₂ =>
      rw [← coe_smul]; rw [← coe_smul]; rw [Completion.dist_eq]; rw [Completion.dist_eq]
      exact dist_smul_pair c x₁ x₂
  dist_pair_smul' c₁ c₂ x := by
    induction x using induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      rw [← coe_smul]; rw [← coe_smul]; rw [Completion.dist_eq]; rw [← coe_zero]; rw [Completion.dist_eq]
      exact dist_pair_smul c₁ c₂ x

end UniformSpace.Completion

open UniformSpace Completion NNReal

/--
theorem `LipschitzWith.completion_extension` / 定理 `LipschitzWith.completion_extension`

English:
theorem LipschitzWith.completion_extension
  statement: [MetricSpace β] [CompleteSpace β] {f : α -> β}
  proof: LipschitzWith.of_dist_le_mul fun x y => induction_on₂ x y
(isClosed_le (by fun_prop) (by fun_prop)) by
      simpa only [extension_coe h.uniformContinuous, Completion.dist_eq] using h.dist_le_mul

中文:
定理 LipschitzWith.completion_extension
  结论: [度量空间 β] [完备空间 β] {f : α -> β}
  证明: LipschitzWith.of_dist_le_mul fun x y => induction_on₂ x y
(isClosed_le (by fun_prop) (by fun_prop)) by
      simpa only [extension_coe h.uniformContinuous, Completion.dist_eq] using h.dist_le_mul

Depends on / 依赖: Completion, Completion.dist_eq, LipschitzWith, LipschitzWith.of_dist_le_mul, dist_eq, dist_le_mul, extension_coe, fun_prop, h.dist_le_mul, h.uniformContinuous, isClosed_le, of_dist_le_mul, uniformContinuous
-/
theorem LipschitzWith.completion_extension [MetricSpace β] [CompleteSpace β] {f : α -> β}
    {K : Real>=0} (h : LipschitzWith K f) : LipschitzWith K (Completion.extension f) :=
  LipschitzWith.of_dist_le_mul fun x y => induction_on₂ x y
(isClosed_le (by fun_prop) (by fun_prop)) by
      simpa only [extension_coe h.uniformContinuous, Completion.dist_eq] using h.dist_le_mul

/--
theorem `LipschitzWith.completion_map` / 定理 `LipschitzWith.completion_map`

English:
theorem LipschitzWith.completion_map
  statement: [PseudoMetricSpace β] {f : α -> β} {K : Real>=0}
  proof: one_mul K ▸ (coe_isometry.lipschitz.comp h).completion_extension

中文:
定理 LipschitzWith.completion_map
  结论: [伪度量空间 β] {f : α -> β} {K : 实数>=0}
  证明: one_mul K ▸ (coe_isometry.lipschitz.comp h).completion_extension

Depends on / 依赖: coe_isometry, coe_isometry.lipschitz.comp, completion_extension, lipschitz, one_mul
-/
theorem LipschitzWith.completion_map [PseudoMetricSpace β] {f : α -> β} {K : Real>=0}
    (h : LipschitzWith K f) : LipschitzWith K (Completion.map f) :=
  one_mul K ▸ (coe_isometry.lipschitz.comp h).completion_extension

/--
theorem `Isometry.completion_extension` / 定理 `Isometry.completion_extension`

English:
theorem Isometry.completion_extension
  statement: [PseudoMetricSpace β] [CompleteSpace β] [T0Space β]
  proof: Isometry.of_dist_eq fun x y => induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun _ _ => by
      simp only [extension_coe h.uniformContinuous, Completion.dist_eq, h.dist_eq]

中文:
定理 等距.completion_extension
  结论: [伪度量空间 β] [完备空间 β] [T0空间 β]
  证明: Isometry.of_dist_eq fun x y => induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun _ _ => by
      simp only [extension_coe h.uniformContinuous, Completion.dist_eq, h.dist_eq]

Depends on / 依赖: Completion, Completion.dist_eq, Isometry, Isometry.of_dist_eq, dist_eq, extension_coe, fun_prop, h.dist_eq, h.uniformContinuous, isClosed_eq, of_dist_eq, uniformContinuous
-/
theorem Isometry.completion_extension [PseudoMetricSpace β] [CompleteSpace β] [T0Space β]
    {f : α -> β} (h : Isometry f) : Isometry (Completion.extension f) :=
  Isometry.of_dist_eq fun x y => induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun _ _ => by
      simp only [extension_coe h.uniformContinuous, Completion.dist_eq, h.dist_eq]

/--
theorem `Isometry.completion_map` / 定理 `Isometry.completion_map`

English:
theorem Isometry.completion_map
  statement: [PseudoMetricSpace β] {f : α -> β}
  proof: (coe_isometry.comp h).completion_extension

中文:
定理 等距.completion_map
  结论: [伪度量空间 β] {f : α -> β}
  证明: (coe_isometry.comp h).completion_extension

Depends on / 依赖: coe_isometry, coe_isometry.comp, completion_extension
-/
theorem Isometry.completion_map [PseudoMetricSpace β] {f : α -> β}
    (h : Isometry f) : Isometry (Completion.map f) :=
  (coe_isometry.comp h).completion_extension

section extension_maps

variable [Ring α] [IsTopologicalRing α] [IsUniformAddGroup α] [Ring β]
    [PseudoMetricSpace β] [IsUniformAddGroup β] [IsTopologicalRing β]

/--
Definition of `Isometry.extensionHom` / `Isometry.extensionHom` 的定义

English:
definition Isometry.extensionHom
  signature: [CompleteSpace β] [T0Space β] {f : α ->+* β} (h : Isometry f)
  body: Completion.extensionHom f h.continuous

@[simp]

中文:
定义 等距.extensionHom
  签名: [完备空间 β] [T0空间 β] {f : α ->+* β} (h : 等距 f)
  定义体: Completion.extensionHom f h.continuous

@[simp]

Depends on / 依赖: Completion, Completion.extensionHom, continuous, extensionHom, h.continuous
-/
def Isometry.extensionHom [CompleteSpace β] [T0Space β] {f : α ->+* β} (h : Isometry f) :
    Completion α ->+* β := Completion.extensionHom f h.continuous

@[simp]
/--
theorem `Isometry.extensionHom_coe` / 定理 `Isometry.extensionHom_coe`

English:
theorem Isometry.extensionHom_coe
  statement: [CompleteSpace β] [T0Space β] {f : α ->+* β} (h : Isometry f)
  proof: Completion.extensionHom_coe f h.continuous _

中文:
定理 等距.extensionHom_coe
  结论: [完备空间 β] [T0空间 β] {f : α ->+* β} (h : 等距 f)
  证明: Completion.extensionHom_coe f h.continuous _

Depends on / 依赖: Completion, Completion.extensionHom_coe, continuous, extensionHom_coe, h.continuous
-/
theorem Isometry.extensionHom_coe [CompleteSpace β] [T0Space β] {f : α ->+* β} (h : Isometry f)
    (x : α) : h.extensionHom x = f x := Completion.extensionHom_coe f h.continuous _

/--
Definition of `Isometry.mapRingHom` / `Isometry.mapRingHom` 的定义

English:
definition Isometry.mapRingHom
  signature: {f : α ->+* β} (h : Isometry f)
  body: Completion.mapRingHom f h.continuous

中文:
定义 等距.mapRingHom
  签名: {f : α ->+* β} (h : 等距 f)
  定义体: Completion.mapRingHom f h.continuous

Depends on / 依赖: Completion, Completion.mapRingHom, continuous, h.continuous, mapRingHom
-/
def Isometry.mapRingHom {f : α ->+* β} (h : Isometry f) : Completion α ->+* Completion β :=
  Completion.mapRingHom f h.continuous

/--
theorem `Isometry.mapRingHom_coe` / 定理 `Isometry.mapRingHom_coe`

English:
theorem Isometry.mapRingHom_coe
  given: {f : α ->+* β} (h : Isometry f) (x : α)
  statement: h.mapRingHom x = f x
  proof: Completion.mapRingHom_coe h.uniformContinuous.continuous _

中文:
定理 等距.mapRingHom_coe
  条件: {f : α ->+* β} (h : 等距 f) (x : α)
  结论: h.mapRingHom x = f x
  证明: Completion.mapRingHom_coe h.uniformContinuous.continuous _

Depends on / 依赖: Completion, Completion.mapRingHom_coe, continuous, h.uniformContinuous.continuous, mapRingHom_coe, uniformContinuous
-/
theorem Isometry.mapRingHom_coe {f : α ->+* β} (h : Isometry f) (x : α) : h.mapRingHom x = f x :=
  Completion.mapRingHom_coe h.uniformContinuous.continuous _

/--
theorem `Isometry.isometry_mapRingHom` / 定理 `Isometry.isometry_mapRingHom`

English:
theorem Isometry.isometry_mapRingHom
  given: {f : α ->+* β} (h : Isometry f)
  statement: Isometry h.mapRingHom
  proof: Isometry.of_dist_eq fun x y => by
    induction x, y using induction_on₂ with
    | hp => exact isClosed_eq (continuous_dist.comp₂ (continuous_map.comp continuous_fst)
        (continuous_map.comp continuous_snd)) (by fun_prop)
    | ih x y => simp only [Completion.dist_eq, mapRingHom_coe, h.dist_eq

中文:
定理 等距.isometry_mapRingHom
  条件: {f : α ->+* β} (h : 等距 f)
  结论: 等距 h.mapRingHom
  证明: Isometry.of_dist_eq fun x y => by
    induction x, y using induction_on₂ with
    | hp => exact isClosed_eq (continuous_dist.comp₂ (continuous_map.comp continuous_fst)
        (continuous_map.comp continuous_snd)) (by fun_prop)
    | ih x y => simp only [Completion.dist_eq, mapRingHom_coe, h.dist_eq

Depends on / 依赖: Completion, Completion.dist_eq, Isometry, Isometry.of_dist_eq, continuous_dist, continuous_dist.comp, continuous_fst, continuous_map, continuous_map.comp, continuous_snd, dist_eq, fun_prop, h.dist_eq, isClosed_eq, mapRingHom_coe, of_dist_eq
-/
theorem Isometry.isometry_mapRingHom {f : α ->+* β} (h : Isometry f) : Isometry h.mapRingHom :=
  Isometry.of_dist_eq fun x y => by
    induction x, y using induction_on₂ with
    | hp => exact isClosed_eq (continuous_dist.comp₂ (continuous_map.comp continuous_fst)
        (continuous_map.comp continuous_snd)) (by fun_prop)
    | ih x y => simp only [Completion.dist_eq, mapRingHom_coe, h.dist_eq]

end extension_maps
