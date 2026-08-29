/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Sequences

/-!
# Continuity of the norm on (semi)normed groups

## Tags

normed group
-/

public section

variable {α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G]

open Finset

section ContinuousENorm

variable {E : Type*} [TopologicalSpace E] [ContinuousENorm E]

@[continuity, fun_prop]
/--
lemma `continuous_enorm` / 引理 `continuous_enorm`

English:
lemma continuous_enorm
  statement: Continuous fun a : E => ‖a‖ₑ
  proof: ContinuousENorm.continuous_enorm

中文:
引理 continuous_enorm
  结论: Continuous fun a : E => ‖a‖ₑ
  证明: ContinuousENorm.continuous_enorm

Depends on / 依赖: ContinuousENorm, ContinuousENorm.continuous_enorm, continuous_enorm
-/
lemma continuous_enorm : Continuous fun a : E => ‖a‖ₑ := ContinuousENorm.continuous_enorm

variable {X : Type*} [TopologicalSpace X] {f : X -> E} {s : Set X} {a : X}

@[fun_prop]
/--
lemma `Continuous.enorm` / 引理 `Continuous.enorm`

English:
lemma Continuous.enorm
  statement: Continuous f -> Continuous (‖f ·‖ₑ)
  proof: continuous_enorm.comp

中文:
引理 Continuous.enorm
  结论: Continuous f -> Continuous (‖f ·‖ₑ)
  证明: continuous_enorm.comp

Depends on / 依赖: continuous_enorm, continuous_enorm.comp
-/
lemma Continuous.enorm : Continuous f -> Continuous (‖f ·‖ₑ) :=
  continuous_enorm.comp

/--
lemma `ContinuousAt.enorm` / 引理 `ContinuousAt.enorm`

English:
lemma ContinuousAt.enorm
  given: {a : X} (h : ContinuousAt f a)
  statement: ContinuousAt (‖f ·‖ₑ) a
  proof: by fun_prop

@[fun_prop]

中文:
引理 ContinuousAt.enorm
  条件: {a : X} (h : ContinuousAt f a)
  结论: ContinuousAt (‖f ·‖ₑ) a
  证明: by fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
lemma ContinuousAt.enorm {a : X} (h : ContinuousAt f a) : ContinuousAt (‖f ·‖ₑ) a := by fun_prop

@[fun_prop]
/--
lemma `ContinuousWithinAt.enorm` / 引理 `ContinuousWithinAt.enorm`

English:
lemma ContinuousWithinAt.enorm
  given: {s : Set X} {a : X} (h : ContinuousWithinAt f s a)
  proof: (ContinuousENorm.continuous_enorm.continuousWithinAt).comp (t := Set.univ) h
    (fun _ _ => by trivial)

@[fun_prop]

中文:
引理 ContinuousWithinAt.enorm
  条件: {s : Set X} {a : X} (h : ContinuousWithinAt f s a)
  证明: (ContinuousENorm.continuous_enorm.continuousWithinAt).comp (t := Set.univ) h
    (fun _ _ => by trivial)

@[fun_prop]

Depends on / 依赖: ContinuousENorm, ContinuousENorm.continuous_enorm.continuousWithinAt, Set.univ, continuousWithinAt, continuous_enorm
-/
lemma ContinuousWithinAt.enorm {s : Set X} {a : X} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (‖f ·‖ₑ) s a :=
  (ContinuousENorm.continuous_enorm.continuousWithinAt).comp (t := Set.univ) h
    (fun _ _ => by trivial)

@[fun_prop]
/--
lemma `ContinuousOn.enorm` / 引理 `ContinuousOn.enorm`

English:
lemma ContinuousOn.enorm
  given: (h : ContinuousOn f s)
  statement: ContinuousOn (‖f ·‖ₑ) s
  proof: (ContinuousENorm.continuous_enorm.continuousOn).comp (t := Set.univ) h Set.mapsTo_univ _ _

中文:
引理 ContinuousOn.enorm
  条件: (h : ContinuousOn f s)
  结论: ContinuousOn (‖f ·‖ₑ) s
  证明: (ContinuousENorm.continuous_enorm.continuousOn).comp (t := Set.univ) h Set.mapsTo_univ _ _

Depends on / 依赖: ContinuousENorm, ContinuousENorm.continuous_enorm.continuousOn, Set.mapsTo_univ, Set.univ, continuousOn, continuous_enorm, mapsTo_univ
-/
lemma ContinuousOn.enorm (h : ContinuousOn f s) : ContinuousOn (‖f ·‖ₑ) s :=
(ContinuousENorm.continuous_enorm.continuousOn).comp (t := Set.univ) h Set.mapsTo_univ _ _

end ContinuousENorm

@[to_additive]
/--
theorem `tendsto_iff_norm_inv_mul_tendsto_zero` / 定理 `tendsto_iff_norm_inv_mul_tendsto_zero`

English:
theorem tendsto_iff_norm_inv_mul_tendsto_zero
  given: {f : α -> E} {a : Filter α} {b : E}
  proof: by
  simp only [← dist_eq_norm_inv_mul, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]

中文:
定理 tendsto_iff_norm_inv_mul_tendsto_zero
  条件: {f : α -> E} {a : Filter α} {b : E}
  证明: by
  simp only [← dist_eq_norm_inv_mul, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]

Depends on / 依赖: dist_eq_norm_inv_mul, tendsto_iff_dist_tendsto_zero
-/
theorem tendsto_iff_norm_inv_mul_tendsto_zero {f : α -> E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖(f e)⁻¹ * b‖) a (𝓝 0) := by
  simp only [← dist_eq_norm_inv_mul, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]
/--
theorem `tendsto_one_iff_norm_tendsto_zero` / 定理 `tendsto_one_iff_norm_tendsto_zero`

English:
theorem tendsto_one_iff_norm_tendsto_zero
  given: {f : α -> E} {a : Filter α}
  proof: tendsto_iff_norm_inv_mul_tendsto_zero.trans by simp

@[to_additive]

中文:
定理 tendsto_one_iff_norm_tendsto_zero
  条件: {f : α -> E} {a : Filter α}
  证明: tendsto_iff_norm_inv_mul_tendsto_zero.trans by simp

@[to_additive]

Depends on / 依赖: tendsto_iff_norm_inv_mul_tendsto_zero, tendsto_iff_norm_inv_mul_tendsto_zero.trans
-/
theorem tendsto_one_iff_norm_tendsto_zero {f : α -> E} {a : Filter α} :
    Tendsto f a (𝓝 1) ↔ Tendsto (‖f ·‖) a (𝓝 0) :=
tendsto_iff_norm_inv_mul_tendsto_zero.trans by simp

@[to_additive]
/--
theorem `tendsto_iff_enorm_inv_mul_tendsto_zero` / 定理 `tendsto_iff_enorm_inv_mul_tendsto_zero`

English:
theorem tendsto_iff_enorm_inv_mul_tendsto_zero
  given: {f : α -> E} {a : Filter α} {b : E}
  proof: by
  simp only [← edist_eq_enorm_inv_mul, ← tendsto_iff_edist_tendsto_0]

@[to_additive]

中文:
定理 tendsto_iff_enorm_inv_mul_tendsto_zero
  条件: {f : α -> E} {a : Filter α} {b : E}
  证明: by
  simp only [← edist_eq_enorm_inv_mul, ← tendsto_iff_edist_tendsto_0]

@[to_additive]

Depends on / 依赖: edist_eq_enorm_inv_mul, tendsto_iff_edist_tendsto_0
-/
theorem tendsto_iff_enorm_inv_mul_tendsto_zero {f : α -> E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖(f e)⁻¹ * b‖ₑ) a (𝓝 0) := by
  simp only [← edist_eq_enorm_inv_mul, ← tendsto_iff_edist_tendsto_0]

@[to_additive]
/--
theorem `tendsto_one_iff_enorm_tendsto_zero` / 定理 `tendsto_one_iff_enorm_tendsto_zero`

English:
theorem tendsto_one_iff_enorm_tendsto_zero
  given: {f : α -> E} {a : Filter α}
  proof: tendsto_iff_enorm_inv_mul_tendsto_zero.trans by simp

@[to_additive (attr := simp 1100)]

中文:
定理 tendsto_one_iff_enorm_tendsto_zero
  条件: {f : α -> E} {a : Filter α}
  证明: tendsto_iff_enorm_inv_mul_tendsto_zero.trans by simp

@[to_additive (attr := simp 1100)]

Depends on / 依赖: tendsto_iff_enorm_inv_mul_tendsto_zero, tendsto_iff_enorm_inv_mul_tendsto_zero.trans
-/
theorem tendsto_one_iff_enorm_tendsto_zero {f : α -> E} {a : Filter α} :
    Tendsto f a (𝓝 1) ↔ Tendsto (‖f ·‖ₑ) a (𝓝 0) :=
tendsto_iff_enorm_inv_mul_tendsto_zero.trans by simp

@[to_additive (attr := simp 1100)]
/--
theorem `comap_norm_nhds_one` / 定理 `comap_norm_nhds_one`

English:
theorem comap_norm_nhds_one
  statement: comap norm (𝓝 0) = 𝓝 (1 : E)
  proof: by
  simpa only [dist_one_right] using nhds_comap_dist (1 : E)

中文:
定理 comap_norm_nhds_one
  结论: comap norm (𝓝 0) = 𝓝 (1 : E)
  证明: by
  simpa only [dist_one_right] using nhds_comap_dist (1 : E)

Depends on / 依赖: dist_one_right, nhds_comap_dist
-/
theorem comap_norm_nhds_one : comap norm (𝓝 0) = 𝓝 (1 : E) := by
  simpa only [dist_one_right] using nhds_comap_dist (1 : E)

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `a` which tends to `0`, then `f` tends to `1` (neutral element of `SeminormedGroup`).
In this pair of lemmas (`squeeze_one_norm'` and `squeeze_one_norm`), following a convention of
similar lemmas in `Topology.MetricSpace.Basic` and `Topology.Algebra.Order`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
@[to_additive /-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by
a real function `a` which tends to `0`, then `f` tends to `0`. In this pair of lemmas
(`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of similar lemmas in
`Topology.MetricSpace.Pseudo.Defs` and `Topology.Algebra.Order`, the `'` version is phrased using
"eventually" and the non-`'` version is phrased absolutely. -/]
/--
theorem `squeeze_one_norm'` / 定理 `squeeze_one_norm'`

English:
theorem squeeze_one_norm'
  statement: {f : α -> E} {a : α -> Real} {t₀ : Filter α} (h : forallᶠ n in t₀, ‖f n‖ <= a n)
  proof: tendsto_one_iff_norm_tendsto_zero.2
    squeeze_zero' (Eventually.of_forall fun _n => norm_nonneg' _) h h'

中文:
定理 squeeze_one_norm'
  结论: {f : α -> E} {a : α -> 实数} {t₀ : Filter α} (h : 对任意ᶠ n in t₀, ‖f n‖ <= a n)
  证明: tendsto_one_iff_norm_tendsto_zero.2
    squeeze_zero' (Eventually.of_forall fun _n => norm_nonneg' _) h h'

Depends on / 依赖: Eventually, Eventually.of_forall, norm_nonneg, of_forall, squeeze_zero, tendsto_one_iff_norm_tendsto_zero
-/
theorem squeeze_one_norm' {f : α -> E} {a : α -> Real} {t₀ : Filter α} (h : forallᶠ n in t₀, ‖f n‖ <= a n)
    (h' : Tendsto a t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 1) :=
tendsto_one_iff_norm_tendsto_zero.2
    squeeze_zero' (Eventually.of_forall fun _n => norm_nonneg' _) h h'

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `a` which
tends to `0`, then `f` tends to `1`. -/
@[to_additive /-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real
function `a` which tends to `0`, then `f` tends to `0`. -/]
/--
theorem `squeeze_one_norm` / 定理 `squeeze_one_norm`

English:
theorem squeeze_one_norm
  given: {f : α -> E} {a : α -> Real} {t₀ : Filter α} (h : forall n, ‖f n‖ <= a n)
  proof: squeeze_one_norm' Eventually.of_forall h

@[to_additive]

中文:
定理 squeeze_one_norm
  条件: {f : α -> E} {a : α -> 实数} {t₀ : Filter α} (h : 对任意 n, ‖f n‖ <= a n)
  证明: squeeze_one_norm' Eventually.of_forall h

@[to_additive]

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, squeeze_one_norm
-/
theorem squeeze_one_norm {f : α -> E} {a : α -> Real} {t₀ : Filter α} (h : forall n, ‖f n‖ <= a n) :
    Tendsto a t₀ (𝓝 0) -> Tendsto f t₀ (𝓝 1) :=
squeeze_one_norm' Eventually.of_forall h

@[to_additive]
/--
theorem `tendsto_norm_inv_mul_self` / 定理 `tendsto_norm_inv_mul_self`

English:
theorem tendsto_norm_inv_mul_self
  given: (x : E)
  statement: Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝 0)
  proof: by
  simpa [dist_eq_norm_inv_mul] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]

中文:
定理 tendsto_norm_inv_mul_self
  条件: (x : E)
  结论: Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝 0)
  证明: by
  simpa [dist_eq_norm_inv_mul] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]

Depends on / 依赖: Tendsto, dist_eq_norm_inv_mul, tendsto_const_nhds, tendsto_id, tendsto_id.dist
-/
theorem tendsto_norm_inv_mul_self (x : E) : Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_inv_mul] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]
/--
theorem `tendsto_norm_inv_mul_self_nhdsGE` / 定理 `tendsto_norm_inv_mul_self_nhdsGE`

English:
theorem tendsto_norm_inv_mul_self_nhdsGE
  given: (x : E)
  statement: Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝[>=] 0)
  proof: tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_inv_mul_self x, by simp⟩

@[to_additive tendsto_norm]

中文:
定理 tendsto_norm_inv_mul_self_nhdsGE
  条件: (x : E)
  结论: Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝[>=] 0)
  证明: tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_inv_mul_self x, by simp⟩

@[to_additive tendsto_norm]

Depends on / 依赖: tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr, tendsto_norm_inv_mul_self
-/
theorem tendsto_norm_inv_mul_self_nhdsGE (x : E) : Tendsto (fun a => ‖a⁻¹ * x‖) (𝓝 x) (𝓝[>=] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_inv_mul_self x, by simp⟩

@[to_additive tendsto_norm]
/--
theorem `tendsto_norm'` / 定理 `tendsto_norm'`

English:
theorem tendsto_norm'
  given: {x : E}
  statement: Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖x‖)
  proof: by
  simpa using tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (1 : E)) _ _)

中文:
定理 tendsto_norm'
  条件: {x : E}
  结论: Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖x‖)
  证明: by
  simpa using tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (1 : E)) _ _)

Depends on / 依赖: Tendsto, tendsto_const_nhds, tendsto_id, tendsto_id.dist
-/
theorem tendsto_norm' {x : E} : Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖x‖) := by
  simpa using tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (1 : E)) _ _)

/-- See `tendsto_norm_one` for a version with pointed neighborhoods. -/
@[to_additive /-- See `tendsto_norm_zero` for a version with pointed neighborhoods. -/]
/--
theorem `tendsto_norm_one` / 定理 `tendsto_norm_one`

English:
theorem tendsto_norm_one
  statement: Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝 0)
  proof: by
  simpa using tendsto_norm_inv_mul_self (1 : E)

@[to_additive (attr := continuity, fun_prop) continuous_norm]

中文:
定理 tendsto_norm_one
  结论: Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝 0)
  证明: by
  simpa using tendsto_norm_inv_mul_self (1 : E)

@[to_additive (attr := continuity, fun_prop) continuous_norm]

Depends on / 依赖: tendsto_norm_inv_mul_self
-/
theorem tendsto_norm_one : Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝 0) := by
  simpa using tendsto_norm_inv_mul_self (1 : E)

@[to_additive (attr := continuity, fun_prop) continuous_norm]
/--
theorem `continuous_norm'` / 定理 `continuous_norm'`

English:
theorem continuous_norm'
  statement: Continuous fun a : E => ‖a‖
  proof: by
  simpa using continuous_id.dist (continuous_const : Continuous fun _a => (1 : E))

@[to_additive (attr := continuity, fun_prop) continuous_nnnorm]

中文:
定理 continuous_norm'
  结论: Continuous fun a : E => ‖a‖
  证明: by
  simpa using continuous_id.dist (continuous_const : Continuous fun _a => (1 : E))

@[to_additive (attr := continuity, fun_prop) continuous_nnnorm]

Depends on / 依赖: Continuous, continuous_const, continuous_id, continuous_id.dist
-/
theorem continuous_norm' : Continuous fun a : E => ‖a‖ := by
  simpa using continuous_id.dist (continuous_const : Continuous fun _a => (1 : E))

@[to_additive (attr := continuity, fun_prop) continuous_nnnorm]
/--
theorem `continuous_nnnorm'` / 定理 `continuous_nnnorm'`

English:
theorem continuous_nnnorm'
  statement: Continuous fun a : E => ‖a‖₊
  proof: continuous_norm'.subtype_mk _

中文:
定理 continuous_nnnorm'
  结论: Continuous fun a : E => ‖a‖₊
  证明: continuous_norm'.subtype_mk _

Depends on / 依赖: continuous_norm, subtype_mk
-/
theorem continuous_nnnorm' : Continuous fun a : E => ‖a‖₊ :=
  continuous_norm'.subtype_mk _

end SeminormedGroup

section Instances

@[to_additive]
/--
Instance `SeminormedGroup.toContinuousENorm` / 实例 `SeminormedGroup.toContinuousENorm`

English:
instance SeminormedGroup.toContinuousENorm
  signature: [SeminormedGroup E]
  body: ENNReal.isOpenEmbedding_coe.continuous.comp continuous_nnnorm'

@[to_additive]

中文:
实例 SeminormedGroup.toContinuousENorm
  签名: [SeminormedGroup E]
  定义体: ENNReal.isOpenEmbedding_coe.continuous.comp continuous_nnnorm'

@[to_additive]

Depends on / 依赖: ENNReal, ENNReal.isOpenEmbedding_coe.continuous.comp, continuous, continuous_nnnorm, isOpenEmbedding_coe
-/
instance SeminormedGroup.toContinuousENorm [SeminormedGroup E] : ContinuousENorm E where
  continuous_enorm := ENNReal.isOpenEmbedding_coe.continuous.comp continuous_nnnorm'

@[to_additive]
/--
Instance `NormedGroup.toENormedMonoid` / 实例 `NormedGroup.toENormedMonoid`

English:
instance NormedGroup.toENormedMonoid
  signature: {F : Type*} [NormedGroup F]
  body: by simp [enorm_eq_nnnorm]
  enorm_eq_zero := by simp [enorm_eq_nnnorm]
  enorm_mul_le := by simp [enorm_eq_nnnorm, ← coe_add, nnnorm_mul_le']

@[to_additive]

中文:
实例 NormedGroup.toENormedMonoid
  签名: {F : 类型} [NormedGroup F]
  定义体: by simp [enorm_eq_nnnorm]
  enorm_eq_zero := by simp [enorm_eq_nnnorm]
  enorm_mul_le := by simp [enorm_eq_nnnorm, ← coe_add, nnnorm_mul_le']

@[to_additive]

Depends on / 依赖: coe_add, enorm_eq_nnnorm, enorm_eq_zero, enorm_mul_le, nnnorm_mul_le
-/
instance NormedGroup.toENormedMonoid {F : Type*} [NormedGroup F] : ENormedMonoid F where
  enorm_zero := by simp [enorm_eq_nnnorm]
  enorm_eq_zero := by simp [enorm_eq_nnnorm]
  enorm_mul_le := by simp [enorm_eq_nnnorm, ← coe_add, nnnorm_mul_le']

@[to_additive]
/--
Instance `NormedCommGroup.toENormedCommMonoid` / 实例 `NormedCommGroup.toENormedCommMonoid`

English:
instance NormedCommGroup.toENormedCommMonoid
  signature: [NormedCommGroup E]
  body: NormedGroup.toENormedMonoid
  __ := ‹NormedCommGroup E›

中文:
实例 NormedCommGroup.toENormedCommMonoid
  签名: [NormedCommGroup E]
  定义体: NormedGroup.toENormedMonoid
  __ := ‹NormedCommGroup E›

Depends on / 依赖: NormedGroup, NormedGroup.toENormedMonoid, toENormedMonoid
-/
instance NormedCommGroup.toENormedCommMonoid [NormedCommGroup E] : ENormedCommMonoid E where
  __ := NormedGroup.toENormedMonoid
  __ := ‹NormedCommGroup E›

end Instances

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E} {a : E}

set_option linter.docPrime false in
@[to_additive Inseparable.norm_eq_norm]
/--
theorem `Inseparable.norm_eq_norm'` / 定理 `Inseparable.norm_eq_norm'`

English:
theorem Inseparable.norm_eq_norm'
  given: {u v : E} (h : Inseparable u v)
  statement: ‖u‖ = ‖v‖
  proof: .eq h.map continuous_norm'

中文:
定理 Inseparable.norm_eq_norm'
  条件: {u v : E} (h : Inseparable u v)
  结论: ‖u‖ = ‖v‖
  证明: .eq h.map continuous_norm'

Depends on / 依赖: continuous_norm, h.map
-/
theorem Inseparable.norm_eq_norm' {u v : E} (h : Inseparable u v) : ‖u‖ = ‖v‖ :=
.eq h.map continuous_norm'

set_option linter.docPrime false in
@[to_additive Inseparable.nnnorm_eq_nnnorm]
/--
theorem `Inseparable.nnnorm_eq_nnnorm'` / 定理 `Inseparable.nnnorm_eq_nnnorm'`

English:
theorem Inseparable.nnnorm_eq_nnnorm'
  given: {u v : E} (h : Inseparable u v)
  statement: ‖u‖₊ = ‖v‖₊
  proof: .eq h.map continuous_nnnorm'

中文:
定理 Inseparable.nnnorm_eq_nnnorm'
  条件: {u v : E} (h : Inseparable u v)
  结论: ‖u‖₊ = ‖v‖₊
  证明: .eq h.map continuous_nnnorm'

Depends on / 依赖: continuous_nnnorm, h.map
-/
theorem Inseparable.nnnorm_eq_nnnorm' {u v : E} (h : Inseparable u v) : ‖u‖₊ = ‖v‖₊ :=
.eq h.map continuous_nnnorm'

/--
theorem `Inseparable.enorm_eq_enorm` / 定理 `Inseparable.enorm_eq_enorm`

English:
theorem Inseparable.enorm_eq_enorm
  statement: {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
  proof: .eq h.map continuous_enorm

@[to_additive]

中文:
定理 Inseparable.enorm_eq_enorm
  结论: {E : 类型} [TopologicalSpace E] [ContinuousENorm E]
  证明: .eq h.map continuous_enorm

@[to_additive]

Depends on / 依赖: continuous_enorm, h.map
-/
theorem Inseparable.enorm_eq_enorm {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {u v : E} (h : Inseparable u v) : ‖u‖ₑ = ‖v‖ₑ :=
.eq h.map continuous_enorm

@[to_additive]
/--
theorem `mem_closure_one_iff_norm` / 定理 `mem_closure_one_iff_norm`

English:
theorem mem_closure_one_iff_norm
  given: {x : E}
  statement: x in closure ({1} : Set E) ↔ ‖x‖ = 0
  proof: by
  rw [← closedBall_zero']; rw [mem_closedBall_one_iff]; rw [(norm_nonneg' x).ge_iff_eq']

@[to_additive]

中文:
定理 mem_closure_one_iff_norm
  条件: {x : E}
  结论: x in closure ({1} : Set E) ↔ ‖x‖ = 0
  证明: by
  rw [← closedBall_zero']; rw [mem_closedBall_one_iff]; rw [(norm_nonneg' x).ge_iff_eq']

@[to_additive]

Depends on / 依赖: closedBall_zero, ge_iff_eq, mem_closedBall_one_iff, norm_nonneg
-/
theorem mem_closure_one_iff_norm {x : E} : x in closure ({1} : Set E) ↔ ‖x‖ = 0 := by
  rw [← closedBall_zero']; rw [mem_closedBall_one_iff]; rw [(norm_nonneg' x).ge_iff_eq']

@[to_additive]
/--
theorem `closure_one_eq` / 定理 `closure_one_eq`

English:
theorem closure_one_eq
  statement: closure ({1} : Set E) = { x | ‖x‖ = 0 }
  proof: Set.ext fun _x => mem_closure_one_iff_norm

中文:
定理 closure_one_eq
  结论: closure ({1} : Set E) = { x | ‖x‖ = 0 }
  证明: Set.ext fun _x => mem_closure_one_iff_norm

Depends on / 依赖: Set.ext, mem_closure_one_iff_norm
-/
theorem closure_one_eq : closure ({1} : Set E) = { x | ‖x‖ = 0 } :=
  Set.ext fun _x => mem_closure_one_iff_norm

section

variable {l : Filter α} {f : α -> E}

@[to_additive Filter.Tendsto.norm]
/--
theorem `Filter.Tendsto.norm'` / 定理 `Filter.Tendsto.norm'`

English:
theorem Filter.Tendsto.norm'
  given: (h : Tendsto f l (𝓝 a))
  statement: Tendsto (fun x => ‖f x‖) l (𝓝 ‖a‖)
  proof: tendsto_norm'.comp h

@[to_additive Filter.Tendsto.nnnorm]

中文:
定理 Filter.Tendsto.norm'
  条件: (h : Tendsto f l (𝓝 a))
  结论: Tendsto (fun x => ‖f x‖) l (𝓝 ‖a‖)
  证明: tendsto_norm'.comp h

@[to_additive Filter.Tendsto.nnnorm]

Depends on / 依赖: tendsto_norm
-/
theorem Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖) l (𝓝 ‖a‖) :=
  tendsto_norm'.comp h

@[to_additive Filter.Tendsto.nnnorm]
/--
theorem `Filter.Tendsto.nnnorm'` / 定理 `Filter.Tendsto.nnnorm'`

English:
theorem Filter.Tendsto.nnnorm'
  given: (h : Tendsto f l (𝓝 a))
  statement: Tendsto (fun x => ‖f x‖₊) l (𝓝 ‖a‖₊)
  proof: Tendsto.comp continuous_nnnorm'.continuousAt h

中文:
定理 Filter.Tendsto.nnnorm'
  条件: (h : Tendsto f l (𝓝 a))
  结论: Tendsto (fun x => ‖f x‖₊) l (𝓝 ‖a‖₊)
  证明: Tendsto.comp continuous_nnnorm'.continuousAt h

Depends on / 依赖: Tendsto, Tendsto.comp, continuousAt, continuous_nnnorm
-/
theorem Filter.Tendsto.nnnorm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖₊) l (𝓝 ‖a‖₊) :=
  Tendsto.comp continuous_nnnorm'.continuousAt h


end

section

variable [TopologicalSpace α] {f : α -> E} {s : Set α} {a : α}

@[to_additive (attr := fun_prop) Continuous.norm]
/--
theorem `Continuous.norm'` / 定理 `Continuous.norm'`

English:
theorem Continuous.norm'
  statement: Continuous f -> Continuous fun x => ‖f x‖
  proof: continuous_norm'.comp

@[to_additive (attr := fun_prop) Continuous.nnnorm]

中文:
定理 Continuous.norm'
  结论: Continuous f -> Continuous fun x => ‖f x‖
  证明: continuous_norm'.comp

@[to_additive (attr := fun_prop) Continuous.nnnorm]

Depends on / 依赖: continuous_norm
-/
theorem Continuous.norm' : Continuous f -> Continuous fun x => ‖f x‖ :=
  continuous_norm'.comp

@[to_additive (attr := fun_prop) Continuous.nnnorm]
/--
theorem `Continuous.nnnorm'` / 定理 `Continuous.nnnorm'`

English:
theorem Continuous.nnnorm'
  statement: Continuous f -> Continuous fun x => ‖f x‖₊
  proof: continuous_nnnorm'.comp

中文:
定理 Continuous.nnnorm'
  结论: Continuous f -> Continuous fun x => ‖f x‖₊
  证明: continuous_nnnorm'.comp

Depends on / 依赖: continuous_nnnorm
-/
theorem Continuous.nnnorm' : Continuous f -> Continuous fun x => ‖f x‖₊ :=
  continuous_nnnorm'.comp

end
end SeminormedGroup

section ContinuousENorm

variable [TopologicalSpace E] [ContinuousENorm E] {a : E} {l : Filter α} {f : α -> E}

/--
lemma `Filter.Tendsto.enorm` / 引理 `Filter.Tendsto.enorm`

English:
lemma Filter.Tendsto.enorm
  given: (h : Tendsto f l (𝓝 a))
  statement: Tendsto (‖f ·‖ₑ) l (𝓝 ‖a‖ₑ)
  proof: .comp continuous_enorm.continuousAt h

中文:
引理 Filter.Tendsto.enorm
  条件: (h : Tendsto f l (𝓝 a))
  结论: Tendsto (‖f ·‖ₑ) l (𝓝 ‖a‖ₑ)
  证明: .comp continuous_enorm.continuousAt h

Depends on / 依赖: continuousAt, continuous_enorm, continuous_enorm.continuousAt
-/
lemma Filter.Tendsto.enorm (h : Tendsto f l (𝓝 a)) : Tendsto (‖f ·‖ₑ) l (𝓝 ‖a‖ₑ) :=
  .comp continuous_enorm.continuousAt h

end ContinuousENorm

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E} {a : E}

section

variable [TopologicalSpace α] {f : α -> E} {s : Set α} {a : α}

@[to_additive (attr := fun_prop) ContinuousAt.norm]
/--
theorem `ContinuousAt.norm'` / 定理 `ContinuousAt.norm'`

English:
theorem ContinuousAt.norm'
  given: {a : α} (h : ContinuousAt f a)
  statement: ContinuousAt (fun x => ‖f x‖) a
  proof: Tendsto.norm' h

@[to_additive (attr := fun_prop) ContinuousAt.nnnorm]

中文:
定理 ContinuousAt.norm'
  条件: {a : α} (h : ContinuousAt f a)
  结论: ContinuousAt (fun x => ‖f x‖) a
  证明: Tendsto.norm' h

@[to_additive (attr := fun_prop) ContinuousAt.nnnorm]

Depends on / 依赖: Tendsto, Tendsto.norm
-/
theorem ContinuousAt.norm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖) a :=
  Tendsto.norm' h

@[to_additive (attr := fun_prop) ContinuousAt.nnnorm]
/--
theorem `ContinuousAt.nnnorm'` / 定理 `ContinuousAt.nnnorm'`

English:
theorem ContinuousAt.nnnorm'
  given: {a : α} (h : ContinuousAt f a)
  statement: ContinuousAt (fun x => ‖f x‖₊) a
  proof: Tendsto.nnnorm' h

@[to_additive ContinuousWithinAt.norm]

中文:
定理 ContinuousAt.nnnorm'
  条件: {a : α} (h : ContinuousAt f a)
  结论: ContinuousAt (fun x => ‖f x‖₊) a
  证明: Tendsto.nnnorm' h

@[to_additive ContinuousWithinAt.norm]

Depends on / 依赖: Tendsto, Tendsto.nnnorm, nnnorm
-/
theorem ContinuousAt.nnnorm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖₊) a :=
  Tendsto.nnnorm' h

@[to_additive ContinuousWithinAt.norm]
/--
theorem `ContinuousWithinAt.norm'` / 定理 `ContinuousWithinAt.norm'`

English:
theorem ContinuousWithinAt.norm'
  given: {s : Set α} {a : α} (h : ContinuousWithinAt f s a)
  proof: Tendsto.norm' h

@[to_additive ContinuousWithinAt.nnnorm]

中文:
定理 ContinuousWithinAt.norm'
  条件: {s : Set α} {a : α} (h : ContinuousWithinAt f s a)
  证明: Tendsto.norm' h

@[to_additive ContinuousWithinAt.nnnorm]

Depends on / 依赖: Tendsto, Tendsto.norm
-/
theorem ContinuousWithinAt.norm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖) s a :=
  Tendsto.norm' h

@[to_additive ContinuousWithinAt.nnnorm]
/--
theorem `ContinuousWithinAt.nnnorm'` / 定理 `ContinuousWithinAt.nnnorm'`

English:
theorem ContinuousWithinAt.nnnorm'
  given: {s : Set α} {a : α} (h : ContinuousWithinAt f s a)
  proof: Tendsto.nnnorm' h

@[to_additive (attr := fun_prop) ContinuousOn.norm]

中文:
定理 ContinuousWithinAt.nnnorm'
  条件: {s : Set α} {a : α} (h : ContinuousWithinAt f s a)
  证明: Tendsto.nnnorm' h

@[to_additive (attr := fun_prop) ContinuousOn.norm]

Depends on / 依赖: Tendsto, Tendsto.nnnorm, nnnorm
-/
theorem ContinuousWithinAt.nnnorm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖₊) s a :=
  Tendsto.nnnorm' h

@[to_additive (attr := fun_prop) ContinuousOn.norm]
/--
theorem `ContinuousOn.norm'` / 定理 `ContinuousOn.norm'`

English:
theorem ContinuousOn.norm'
  given: {s : Set α} (h : ContinuousOn f s)
  statement: ContinuousOn (fun x => ‖f x‖) s
  proof: fun x hx => (h x hx).norm'

@[to_additive (attr := fun_prop) ContinuousOn.nnnorm]

中文:
定理 ContinuousOn.norm'
  条件: {s : Set α} (h : ContinuousOn f s)
  结论: ContinuousOn (fun x => ‖f x‖) s
  证明: fun x hx => (h x hx).norm'

@[to_additive (attr := fun_prop) ContinuousOn.nnnorm]
-/
theorem ContinuousOn.norm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fun x => ‖f x‖) s :=
  fun x hx => (h x hx).norm'

@[to_additive (attr := fun_prop) ContinuousOn.nnnorm]
/--
theorem `ContinuousOn.nnnorm'` / 定理 `ContinuousOn.nnnorm'`

English:
theorem ContinuousOn.nnnorm'
  given: {s : Set α} (h : ContinuousOn f s)
  proof: fun x hx => (h x hx).nnnorm'

中文:
定理 ContinuousOn.nnnorm'
  条件: {s : Set α} (h : ContinuousOn f s)
  证明: fun x hx => (h x hx).nnnorm'

Depends on / 依赖: nnnorm
-/
theorem ContinuousOn.nnnorm' {s : Set α} (h : ContinuousOn f s) :
    ContinuousOn (fun x => ‖f x‖₊) s := fun x hx => (h x hx).nnnorm'

end

/-- If `‖y‖ → ∞`, then we can assume `y ≠ x` for any fixed `x`. -/
@[to_additive eventually_ne_of_tendsto_norm_atTop /-- If `‖y‖→∞`, then we can assume `y≠x` for any
fixed `x` -/]
/--
theorem `eventually_ne_of_tendsto_norm_atTop'` / 定理 `eventually_ne_of_tendsto_norm_atTop'`

English:
theorem eventually_ne_of_tendsto_norm_atTop'
  statement: {l : Filter α} {f : α -> E}
  proof: (h.eventually_ne_atTop _).mono fun _x => ne_of_apply_ne norm

@[to_additive]

中文:
定理 eventually_ne_of_tendsto_norm_atTop'
  结论: {l : Filter α} {f : α -> E}
  证明: (h.eventually_ne_atTop _).mono fun _x => ne_of_apply_ne norm

@[to_additive]

Depends on / 依赖: eventually_ne_atTop, h.eventually_ne_atTop, ne_of_apply_ne
-/
theorem eventually_ne_of_tendsto_norm_atTop' {l : Filter α} {f : α -> E}
    (h : Tendsto (fun y => ‖f y‖) l atTop) (x : E) : forallᶠ y in l, f y != x :=
  (h.eventually_ne_atTop _).mono fun _x => ne_of_apply_ne norm

@[to_additive]
/--
theorem `SeminormedGroup.mem_closure_iff` / 定理 `SeminormedGroup.mem_closure_iff`

English:
theorem SeminormedGroup.mem_closure_iff
  proof: by
  simp [Metric.mem_closure_iff, dist_eq_norm_inv_mul]

@[to_additive]

中文:
定理 SeminormedGroup.mem_closure_iff
  证明: by
  simp [Metric.mem_closure_iff, dist_eq_norm_inv_mul]

@[to_additive]

Depends on / 依赖: Metric, Metric.mem_closure_iff, dist_eq_norm_inv_mul, mem_closure_iff
-/
theorem SeminormedGroup.mem_closure_iff :
    a in closure s ↔ forall ε, 0 < ε -> exists b in s, ‖a⁻¹ * b‖ < ε := by
  simp [Metric.mem_closure_iff, dist_eq_norm_inv_mul]

@[to_additive]
/--
theorem `SeminormedGroup.tendstoUniformlyOn_one` / 定理 `SeminormedGroup.tendstoUniformlyOn_one`

English:
theorem SeminormedGroup.tendstoUniformlyOn_one
  given: {f : ι -> κ -> G} {s : Set κ} {l : Filter ι}
  proof: by
  simp only [tendstoUniformlyOn_iff, Pi.one_apply, dist_one_left]

@[to_additive]

中文:
定理 SeminormedGroup.tendstoUniformlyOn_one
  条件: {f : ι -> κ -> G} {s : Set κ} {l : Filter ι}
  证明: by
  simp only [tendstoUniformlyOn_iff, Pi.one_apply, dist_one_left]

@[to_additive]

Depends on / 依赖: Pi.one_apply, dist_one_left, one_apply, tendstoUniformlyOn_iff
-/
theorem SeminormedGroup.tendstoUniformlyOn_one {f : ι -> κ -> G} {s : Set κ} {l : Filter ι} :
    TendstoUniformlyOn f 1 l s ↔ forall ε > 0, forallᶠ i in l, forall x in s, ‖f i x‖ < ε := by
  simp only [tendstoUniformlyOn_iff, Pi.one_apply, dist_one_left]

@[to_additive]
/--
theorem `SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one` / 定理 `SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one`

English:
theorem SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one
  statement: {f : ι -> κ -> G}
  proof: by
  refine ⟨fun hf u hu => ?_, fun hf u hu => ?_⟩
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H 1 ((f x.fst.fst x.snd)⁻¹ * f x.fst.snd x.snd) ?_
    simpa [dist_

中文:
定理 SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one
  结论: {f : ι -> κ -> G}
  证明: by
  refine ⟨fun hf u hu => ?_, fun hf u hu => ?_⟩
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H 1 ((f x.fst.fst x.snd)⁻¹ * f x.fst.snd x.snd) ?_
    simpa [dist_

Depends on / 依赖: dist_eq_norm_inv_mul, dist_mem_uniformity, mem_uniformity_iff, norm_div_rev, p.fst, p.snd, uniformity_basis_dist, uniformity_basis_dist.mem_uniformity_iff.mp, x.fst.fst, x.fst.snd, x.snd
-/
theorem SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one {f : ι -> κ -> G}
    {l : Filter ι} {l' : Filter κ} :
    UniformCauchySeqOnFilter f l l' ↔ TendstoUniformlyOnFilter
      (fun n : ι × ι => fun z => (f n.fst z)⁻¹ * f n.snd z) 1 (l ×ˢ l) l' := by
  refine ⟨fun hf u hu => ?_, fun hf u hu => ?_⟩
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H 1 ((f x.fst.fst x.snd)⁻¹ * f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_inv_mul, norm_div_rev] using hx
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H (f x.fst.fst x.snd) (f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_inv_mul, norm_div_rev] using hx

@[to_additive]
/--
theorem `SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one` / 定理 `SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one`

English:
theorem SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one
  statement: {f : ι -> κ -> G} {s : Set κ}
  proof: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]; rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter]; rw [SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one]

中文:
定理 SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one
  结论: {f : ι -> κ -> G} {s : Set κ}
  证明: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]; rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter]; rw [SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one]

Depends on / 依赖: SeminormedGroup, SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one, uniformCauchySeqOn_iff_uniformCauchySeqOnFilter
-/
theorem SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one {f : ι -> κ -> G} {s : Set κ}
    {l : Filter ι} :
    UniformCauchySeqOn f l s ↔
      TendstoUniformlyOn (fun n : ι × ι => fun z => (f n.fst z)⁻¹ * f n.snd z) 1 (l ×ˢ l) s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]; rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter]; rw [SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one]

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : Real}

@[to_additive]
/--
theorem `tendsto_iff_norm_div_tendsto_zero` / 定理 `tendsto_iff_norm_div_tendsto_zero`

English:
theorem tendsto_iff_norm_div_tendsto_zero
  given: {f : α -> E} {a : Filter α} {b : E}
  proof: by
  simp only [← dist_eq_norm_div, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]

中文:
定理 tendsto_iff_norm_div_tendsto_zero
  条件: {f : α -> E} {a : Filter α} {b : E}
  证明: by
  simp only [← dist_eq_norm_div, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]

Depends on / 依赖: dist_eq_norm_div, tendsto_iff_dist_tendsto_zero
-/
theorem tendsto_iff_norm_div_tendsto_zero {f : α -> E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖) a (𝓝 0) := by
  simp only [← dist_eq_norm_div, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]
/--
theorem `tendsto_iff_enorm_div_tendsto_zero` / 定理 `tendsto_iff_enorm_div_tendsto_zero`

English:
theorem tendsto_iff_enorm_div_tendsto_zero
  given: {f : α -> E} {a : Filter α} {b : E}
  proof: by
  simp only [← edist_eq_enorm_div, ← tendsto_iff_edist_tendsto_0]

@[to_additive]

中文:
定理 tendsto_iff_enorm_div_tendsto_zero
  条件: {f : α -> E} {a : Filter α} {b : E}
  证明: by
  simp only [← edist_eq_enorm_div, ← tendsto_iff_edist_tendsto_0]

@[to_additive]

Depends on / 依赖: edist_eq_enorm_div, tendsto_iff_edist_tendsto_0
-/
theorem tendsto_iff_enorm_div_tendsto_zero {f : α -> E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖ₑ) a (𝓝 0) := by
  simp only [← edist_eq_enorm_div, ← tendsto_iff_edist_tendsto_0]

@[to_additive]
/--
theorem `SeminormedCommGroup.mem_closure_iff` / 定理 `SeminormedCommGroup.mem_closure_iff`

English:
theorem SeminormedCommGroup.mem_closure_iff
  given: {s : Set E}
  proof: by
  simp [Metric.mem_closure_iff, dist_eq_norm_div]

@[to_additive]

中文:
定理 SeminormedCommGroup.mem_closure_iff
  条件: {s : Set E}
  证明: by
  simp [Metric.mem_closure_iff, dist_eq_norm_div]

@[to_additive]

Depends on / 依赖: Metric, Metric.mem_closure_iff, dist_eq_norm_div, mem_closure_iff
-/
theorem SeminormedCommGroup.mem_closure_iff {s : Set E} :
    a in closure s ↔ forall ε, 0 < ε -> exists b in s, ‖a / b‖ < ε := by
  simp [Metric.mem_closure_iff, dist_eq_norm_div]

@[to_additive]
/--
theorem `tendsto_norm_div_self` / 定理 `tendsto_norm_div_self`

English:
theorem tendsto_norm_div_self
  given: (x : E)
  statement: Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝 0)
  proof: by
  simpa [dist_eq_norm_div] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]

中文:
定理 tendsto_norm_div_self
  条件: (x : E)
  结论: Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝 0)
  证明: by
  simpa [dist_eq_norm_div] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]

Depends on / 依赖: Tendsto, dist_eq_norm_div, tendsto_const_nhds, tendsto_id, tendsto_id.dist
-/
theorem tendsto_norm_div_self (x : E) : Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_div] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive]
/--
theorem `tendsto_norm_div_self_nhdsGE` / 定理 `tendsto_norm_div_self_nhdsGE`

English:
theorem tendsto_norm_div_self_nhdsGE
  given: (x : E)
  statement: Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝[>=] 0)
  proof: tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_div_self x, by simp⟩

中文:
定理 tendsto_norm_div_self_nhdsGE
  条件: (x : E)
  结论: Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝[>=] 0)
  证明: tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_div_self x, by simp⟩

Depends on / 依赖: tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr, tendsto_norm_div_self
-/
theorem tendsto_norm_div_self_nhdsGE (x : E) : Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝[>=] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_div_self x, by simp⟩

open Finset

@[to_additive]
/--
theorem `controlled_prod_of_mem_closure` / 定理 `controlled_prod_of_mem_closure`

English:
theorem controlled_prod_of_mem_closure
  statement: {s : Subgroup E} (hg : a in closure (s : Set E)) {b : Nat -> Real}
  proof: by
  obtain ⟨u : Nat -> E, u_in : forall n, u n in s, lim_u : Tendsto u atTop (𝓝 a)⟩ :=
    mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : exists n₀, forall n >= n₀, ‖(u n)⁻¹ * a‖ < b 0 :=
    haveI : { x | ‖x⁻¹ * a‖ < b 0 } in 𝓝 a := by
      simp_rw [← dist_eq_norm_inv_mul]
      exact Metri

中文:
定理 controlled_prod_of_mem_closure
  结论: {s : Subgroup E} (hg : a in closure (s : Set E)) {b : 自然数 -> 实数}
  证明: by
  obtain ⟨u : Nat -> E, u_in : forall n, u n in s, lim_u : Tendsto u atTop (𝓝 a)⟩ :=
    mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : exists n₀, forall n >= n₀, ‖(u n)⁻¹ * a‖ < b 0 :=
    haveI : { x | ‖x⁻¹ * a‖ < b 0 } in 𝓝 a := by
      simp_rw [← dist_eq_norm_inv_mul]
      exact Metri

Depends on / 依赖: Filter, Filter.tendsto_atTop, Metric, Metric.ball_mem_nhds, Tendsto, b_pos, ball_mem_nhds, dist_eq_norm_inv_mul, lim_u, lim_u.comp, lim_z, mem_closure_iff_seq_limit, mem_closure_iff_seq_limit.mp, simp_rw, tendsto_add_atTop_nat, tendsto_atTop, u_in
-/
theorem controlled_prod_of_mem_closure {s : Subgroup E} (hg : a in closure (s : Set E)) {b : Nat -> Real}
    (b_pos : forall n, 0 < b n) :
    exists v : Nat -> E,
      Tendsto (fun n => ∏ i in range (n + 1), v i) atTop (𝓝 a) ∧
        (forall n, v n in s) ∧ ‖(v 0)⁻¹ * a‖ < b 0 ∧ forall n, 0 < n -> ‖v n‖ < b n := by
  obtain ⟨u : Nat -> E, u_in : forall n, u n in s, lim_u : Tendsto u atTop (𝓝 a)⟩ :=
    mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : exists n₀, forall n >= n₀, ‖(u n)⁻¹ * a‖ < b 0 :=
    haveI : { x | ‖x⁻¹ * a‖ < b 0 } in 𝓝 a := by
      simp_rw [← dist_eq_norm_inv_mul]
      exact Metric.ball_mem_nhds _ (b_pos _)
    Filter.tendsto_atTop'.mp lim_u _ this
  set z : Nat -> E := fun n => u (n + n₀)
  have lim_z : Tendsto z atTop (𝓝 a) := lim_u.comp (tendsto_add_atTop_nat n₀)
  have mem_𝓤 : forall n, { p : E × E | ‖p.1⁻¹ * p.2‖ < b (n + 1) } in 𝓤 E := fun n => by
    simpa [← dist_eq_norm_inv_mul] using Metric.dist_mem_uniformity (b_pos <| n + 1)
  obtain ⟨φ : Nat -> Nat, φ_extr : StrictMono φ, hφ : forall n, ‖(z (φ (n + 1)))⁻¹ * z (φ n)‖ < b (n + 1)⟩ :=
    lim_z.cauchySeq.subseq_mem mem_𝓤
  set w : Nat -> E := z ∘ φ
  have hw : Tendsto w atTop (𝓝 a) := lim_z.comp φ_extr.tendsto_atTop
  set v : Nat -> E := fun i => if i = 0 then w 0 else (w (i - 1))⁻¹ * w i
  refine ⟨v, ?_, ?_, hn₀ _ (n₀.le_add_left _), ?_⟩
  · apply hw.congr (fun n => ?_)
    rw [Finset.prod_range_succ']
    have : ∏ k in range n, v (k + 1) = (v 0)⁻¹ * w n := by
      apply prod_range_induction _ _ (by simp [v]) _ (fun k hk => ?_)
      simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, add_tsub_cancel_right, v]
      group
    simp [this]
  · rintro ⟨⟩
    · change w 0 in s
      apply u_in
    · exact s.mul_mem (s.inv_mem (u_in _)) (u_in _)
  · intro l hl
    obtain ⟨k, rfl⟩ : exists k, l = k + 1 := Nat.exists_eq_succ_of_ne_zero hl.ne'
    rw [← norm_inv']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      mul_inv_rev, inv_inv, v]
    apply hφ

@[to_additive]
/--
theorem `controlled_prod_of_mem_closure_range` / 定理 `controlled_prod_of_mem_closure_range`

English:
theorem controlled_prod_of_mem_closure_range
  statement: {j : E ->* F} {b : F}
  proof: by
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos
  choose g hg using v_in
  exact
    ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀,
      fun n hn => by simpa [hg] using hv_pos n hn⟩

中文:
定理 controlled_prod_of_mem_closure_range
  结论: {j : E ->* F} {b : F}
  证明: by
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos
  choose g hg using v_in
  exact
    ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀,
      fun n hn => by simpa [hg] using hv_pos n hn⟩

Depends on / 依赖: b_pos, controlled_prod_of_mem_closure, hv_pos, sum_v, v_in
-/
theorem controlled_prod_of_mem_closure_range {j : E ->* F} {b : F}
    (hb : b in closure (j.range : Set F)) {f : Nat -> Real} (b_pos : forall n, 0 < f n) :
    exists a : Nat -> E,
      Tendsto (fun n => ∏ i in range (n + 1), j (a i)) atTop (𝓝 b) ∧
        ‖(j (a 0))⁻¹ * b‖ < f 0 ∧ forall n, 0 < n -> ‖j (a n)‖ < f n := by
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos
  choose g hg using v_in
  exact
    ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀,
      fun n hn => by simpa [hg] using hv_pos n hn⟩

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] {a b : E}

/-- See `tendsto_norm_one` for a version with full neighborhoods. -/
@[to_additive /-- See `tendsto_norm_zero` for a version with full neighborhoods. -/]
/--
lemma `tendsto_norm_nhdsNE_one` / 引理 `tendsto_norm_nhdsNE_one`

English:
lemma tendsto_norm_nhdsNE_one
  statement: Tendsto (norm : E -> Real) (𝓝[!=] 1) (𝓝[>] 0)
  proof: tendsto_norm_one.inf tendsto_principal_principal.2 fun _ hx => norm_pos_iff'.2 hx

@[to_additive]

中文:
引理 tendsto_norm_nhdsNE_one
  结论: Tendsto (norm : E -> 实数) (𝓝[!=] 1) (𝓝[>] 0)
  证明: tendsto_norm_one.inf tendsto_principal_principal.2 fun _ hx => norm_pos_iff'.2 hx

@[to_additive]

Depends on / 依赖: norm_pos_iff, tendsto_norm_one, tendsto_norm_one.inf, tendsto_principal_principal
-/
lemma tendsto_norm_nhdsNE_one : Tendsto (norm : E -> Real) (𝓝[!=] 1) (𝓝[>] 0) :=
tendsto_norm_one.inf tendsto_principal_principal.2 fun _ hx => norm_pos_iff'.2 hx

@[to_additive]
/--
theorem `tendsto_norm_inv_mul_self_nhdsNE` / 定理 `tendsto_norm_inv_mul_self_nhdsNE`

English:
theorem tendsto_norm_inv_mul_self_nhdsNE
  given: (a : E)
  proof: by
  apply (tendsto_norm_inv_mul_self a).inf
  apply tendsto_principal_principal.2 (fun _x hx => norm_pos_iff'.2 ?_)
  simpa [inv_mul_eq_one] using hx

中文:
定理 tendsto_norm_inv_mul_self_nhdsNE
  条件: (a : E)
  证明: by
  apply (tendsto_norm_inv_mul_self a).inf
  apply tendsto_principal_principal.2 (fun _x hx => norm_pos_iff'.2 ?_)
  simpa [inv_mul_eq_one] using hx

Depends on / 依赖: inv_mul_eq_one, norm_pos_iff, tendsto_norm_inv_mul_self, tendsto_principal_principal
-/
theorem tendsto_norm_inv_mul_self_nhdsNE (a : E) :
    Tendsto (fun x => ‖x⁻¹ * a‖) (𝓝[!=] a) (𝓝[>] 0) := by
  apply (tendsto_norm_inv_mul_self a).inf
  apply tendsto_principal_principal.2 (fun _x hx => norm_pos_iff'.2 ?_)
  simpa [inv_mul_eq_one] using hx

variable (E)

/-- In a normed group, the pullback under the norm of `𝓝[>] 0` is the punctured neighborhood
of `1`. -/
@[to_additive comap_norm_nhdsGT_zero
/-- In a normed additive group, the pullback under the norm of `𝓝[>] 0` is the punctured
neighborhood of `0`. -/]
/--
lemma `comap_norm_nhdsGT_zero'` / 引理 `comap_norm_nhdsGT_zero'`

English:
lemma comap_norm_nhdsGT_zero'
  statement: comap norm (𝓝[>] 0) = 𝓝[!=] (1 : E)
  proof: by
  simp [nhdsWithin, comap_norm_nhds_one, Set.preimage, Set.compl_def]

@[to_additive]

中文:
引理 comap_norm_nhdsGT_zero'
  结论: comap norm (𝓝[>] 0) = 𝓝[!=] (1 : E)
  证明: by
  simp [nhdsWithin, comap_norm_nhds_one, Set.preimage, Set.compl_def]

@[to_additive]

Depends on / 依赖: Set.compl_def, Set.preimage, comap_norm_nhds_one, compl_def, nhdsWithin, preimage
-/
lemma comap_norm_nhdsGT_zero' : comap norm (𝓝[>] 0) = 𝓝[!=] (1 : E) := by
  simp [nhdsWithin, comap_norm_nhds_one, Set.preimage, Set.compl_def]

@[to_additive]
/--
theorem `tendsto_norm_div_self_nhdsNE` / 定理 `tendsto_norm_div_self_nhdsNE`

English:
theorem tendsto_norm_div_self_nhdsNE
  given: {E : Type*} [NormedCommGroup E] (a : E)
  proof: by
  simp_rw [← norm_inv_mul]
  exact tendsto_norm_inv_mul_self_nhdsNE a

中文:
定理 tendsto_norm_div_self_nhdsNE
  条件: {E : 类型} [NormedCommGroup E] (a : E)
  证明: by
  simp_rw [← norm_inv_mul]
  exact tendsto_norm_inv_mul_self_nhdsNE a

Depends on / 依赖: norm_inv_mul, simp_rw, tendsto_norm_inv_mul_self_nhdsNE
-/
theorem tendsto_norm_div_self_nhdsNE {E : Type*} [NormedCommGroup E] (a : E) :
    Tendsto (fun x => ‖x / a‖) (𝓝[!=] a) (𝓝[>] 0) := by
  simp_rw [← norm_inv_mul]
  exact tendsto_norm_inv_mul_self_nhdsNE a

end NormedGroup
