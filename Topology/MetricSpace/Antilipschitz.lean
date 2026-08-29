/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Antilipschitz functions

We say that a map `f : α → β` between two (extended) metric spaces is
`AntilipschitzWith K`, `K ≥ 0`, if for all `x, y` we have `edist x y ≤ K * edist (f x) (f y)`.
For a metric space, the latter inequality is equivalent to `dist x y ≤ K * dist (f x) (f y)`.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. We do not require `0 < K` in the definition, mostly because
we do not have a `posreal` type.
-/

@[expose] public section

open Bornology Filter Set Topology
open scoped NNReal ENNReal Uniformity

variable {α β γ : Type*}

/--
Definition of `AntilipschitzWith` / `AntilipschitzWith` 的定义

English:
definition AntilipschitzWith
  signature: [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : Real>=0) (f : α -> β)
  body: forall x y, edist x y <= K * edist (f x) (f y)

中文:
定义 AntilipschitzWith
  签名: [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : 实数>=0) (f : α -> β)
  定义体: forall x y, edist x y <= K * edist (f x) (f y)
-/
def AntilipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : Real>=0) (f : α -> β) :=
  forall x y, edist x y <= K * edist (f x) (f y)

/--
lemma `AntilipschitzWith.edist_lt_top` / 引理 `AntilipschitzWith.edist_lt_top`

English:
lemma AntilipschitzWith.edist_lt_top
  statement: [PseudoEMetricSpace α] [PseudoMetricSpace β]
  proof: (h x y).trans_lt ENNReal.mul_lt_top ENNReal.coe_lt_top (edist_lt_top _ _)

中文:
引理 AntilipschitzWith.edist_lt_top
  结论: [PseudoEMetricSpace α] [PseudoMetricSpace β]
  证明: (h x y).trans_lt ENNReal.mul_lt_top ENNReal.coe_lt_top (edist_lt_top _ _)
-/
protected lemma AntilipschitzWith.edist_lt_top [PseudoEMetricSpace α] [PseudoMetricSpace β]
    {K : Real>=0} {f : α -> β} (h : AntilipschitzWith K f) (x y : α) : edist x y < ⊤ :=
(h x y).trans_lt ENNReal.mul_lt_top ENNReal.coe_lt_top (edist_lt_top _ _)

/--
theorem `AntilipschitzWith.edist_ne_top` / 定理 `AntilipschitzWith.edist_ne_top`

English:
theorem AntilipschitzWith.edist_ne_top
  statement: [PseudoEMetricSpace α] [PseudoMetricSpace β] {K : Real>=0}
  proof: (h.edist_lt_top x y).ne

中文:
定理 AntilipschitzWith.edist_ne_top
  结论: [PseudoEMetricSpace α] [PseudoMetricSpace β] {K : 实数>=0}
  证明: (h.edist_lt_top x y).ne

Depends on / 依赖: edist_lt_top, h.edist_lt_top
-/
theorem AntilipschitzWith.edist_ne_top [PseudoEMetricSpace α] [PseudoMetricSpace β] {K : Real>=0}
    {f : α -> β} (h : AntilipschitzWith K f) (x y : α) : edist x y != ⊤ :=
  (h.edist_lt_top x y).ne

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {K : Real>=0} {f : α -> β}

/--
theorem `antilipschitzWith_iff_le_mul_nndist` / 定理 `antilipschitzWith_iff_le_mul_nndist`

English:
theorem antilipschitzWith_iff_le_mul_nndist
  proof: by
  simp only [AntilipschitzWith, edist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_nndist, AntilipschitzWith.of_le_mul_nndist⟩ :=
  antilipschitzWith_iff_le_mul_nndist

中文:
定理 antilipschitzWith_iff_le_mul_nndist
  证明: by
  simp only [AntilipschitzWith, edist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_nndist, AntilipschitzWith.of_le_mul_nndist⟩ :=
  antilipschitzWith_iff_le_mul_nndist

Depends on / 依赖: AntilipschitzWith, edist_nndist
-/
theorem antilipschitzWith_iff_le_mul_nndist :
    AntilipschitzWith K f ↔ forall x y, nndist x y <= K * nndist (f x) (f y) := by
  simp only [AntilipschitzWith, edist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_nndist, AntilipschitzWith.of_le_mul_nndist⟩ :=
  antilipschitzWith_iff_le_mul_nndist

/--
theorem `antilipschitzWith_iff_le_mul_dist` / 定理 `antilipschitzWith_iff_le_mul_dist`

English:
theorem antilipschitzWith_iff_le_mul_dist
  proof: by
  simp only [antilipschitzWith_iff_le_mul_nndist, dist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_dist, AntilipschitzWith.of_le_mul_dist⟩ :=
  antilipschitzWith_iff_le_mul_dist

中文:
定理 antilipschitzWith_iff_le_mul_dist
  证明: by
  simp only [antilipschitzWith_iff_le_mul_nndist, dist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_dist, AntilipschitzWith.of_le_mul_dist⟩ :=
  antilipschitzWith_iff_le_mul_dist

Depends on / 依赖: antilipschitzWith_iff_le_mul_nndist, dist_nndist
-/
theorem antilipschitzWith_iff_le_mul_dist :
    AntilipschitzWith K f ↔ forall x y, dist x y <= K * dist (f x) (f y) := by
  simp only [antilipschitzWith_iff_le_mul_nndist, dist_nndist]
  norm_cast

alias ⟨AntilipschitzWith.le_mul_dist, AntilipschitzWith.of_le_mul_dist⟩ :=
  antilipschitzWith_iff_le_mul_dist

namespace AntilipschitzWith

/--
theorem `mul_le_nndist` / 定理 `mul_le_nndist`

English:
theorem mul_le_nndist
  given: (hf : AntilipschitzWith K f) (x y : α)
  proof: by
  simpa only [div_eq_inv_mul] using NNReal.div_le_of_le_mul' (hf.le_mul_nndist x y)

中文:
定理 mul_le_nndist
  条件: (hf : AntilipschitzWith K f) (x y : α)
  证明: by
  simpa only [div_eq_inv_mul] using NNReal.div_le_of_le_mul' (hf.le_mul_nndist x y)

Depends on / 依赖: NNReal, NNReal.div_le_of_le_mul, div_eq_inv_mul, div_le_of_le_mul, hf.le_mul_nndist, le_mul_nndist
-/
theorem mul_le_nndist (hf : AntilipschitzWith K f) (x y : α) :
    K⁻¹ * nndist x y <= nndist (f x) (f y) := by
  simpa only [div_eq_inv_mul] using NNReal.div_le_of_le_mul' (hf.le_mul_nndist x y)

/--
theorem `mul_le_dist` / 定理 `mul_le_dist`

English:
theorem mul_le_dist
  given: (hf : AntilipschitzWith K f) (x y : α)
  proof: mod_cast hf.mul_le_nndist x y

中文:
定理 mul_le_dist
  条件: (hf : AntilipschitzWith K f) (x y : α)
  证明: mod_cast hf.mul_le_nndist x y

Depends on / 依赖: hf.mul_le_nndist, mod_cast, mul_le_nndist
-/
theorem mul_le_dist (hf : AntilipschitzWith K f) (x y : α) :
    (K⁻¹ * dist x y : Real) <= dist (f x) (f y) := mod_cast hf.mul_le_nndist x y

end AntilipschitzWith

end Metric

namespace AntilipschitzWith

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {K : Real>=0} {f : α -> β}

open Metric

-- uses neither `f` nor `hf`
/-- Extract the constant from `hf : AntilipschitzWith K f`. This is useful, e.g.,
if `K` is given by a long formula, and we want to reuse this value. -/
@[nolint unusedArguments]
/--
Definition of `k` / `k` 的定义

English:
definition k
  signature: (_hf : AntilipschitzWith K f)
  body: K

中文:
定义 k
  签名: (_hf : AntilipschitzWith K f)
  定义体: K
-/
protected def k (_hf : AntilipschitzWith K f) : Real>=0 := K

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: {α : Type*} {β : Type*} [EMetricSpace α] [PseudoEMetricSpace β]
  proof: fun x y h => by
  simpa only [h, edist_self, mul_zero, edist_le_zero] using hf x y

中文:
定理 injective
  结论: {α : 类型} {β : 类型} [EMetricSpace α] [PseudoEMetricSpace β]
  证明: fun x y h => by
  simpa only [h, edist_self, mul_zero, edist_le_zero] using hf x y
-/
protected theorem injective {α : Type*} {β : Type*} [EMetricSpace α] [PseudoEMetricSpace β]
    {K : Real>=0} {f : α -> β} (hf : AntilipschitzWith K f) : Function.Injective f := fun x y h => by
  simpa only [h, edist_self, mul_zero, edist_le_zero] using hf x y

/--
theorem `mul_le_edist` / 定理 `mul_le_edist`

English:
theorem mul_le_edist
  given: (hf : AntilipschitzWith K f) (x y : α)
  proof: by
  rw [mul_comm]; rw [← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (hf x y)

中文:
定理 mul_le_edist
  条件: (hf : AntilipschitzWith K f) (x y : α)
  证明: by
  rw [mul_comm]; rw [← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (hf x y)

Depends on / 依赖: ENNReal, ENNReal.div_le_of_le_mul, div_eq_mul_inv, div_le_of_le_mul, mul_comm
-/
theorem mul_le_edist (hf : AntilipschitzWith K f) (x y : α) :
    (K : Real>=0∞)⁻¹ * edist x y <= edist (f x) (f y) := by
  rw [mul_comm]; rw [← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (hf x y)

/--
theorem `ediam_preimage_le` / 定理 `ediam_preimage_le`

English:
theorem ediam_preimage_le
  given: (hf : AntilipschitzWith K f) (s : Set β)
  proof: ediam_le fun x hx y hy => by grw [hf x y, edist_le_ediam_of_mem (mem_preimage.1 hx) hy]

中文:
定理 ediam_preimage_le
  条件: (hf : AntilipschitzWith K f) (s : Set β)
  证明: ediam_le fun x hx y hy => by grw [hf x y, edist_le_ediam_of_mem (mem_preimage.1 hx) hy]

Depends on / 依赖: ediam_le, edist_le_ediam_of_mem, mem_preimage
-/
theorem ediam_preimage_le (hf : AntilipschitzWith K f) (s : Set β) :
    ediam (f ⁻¹' s) <= K * ediam s :=
  ediam_le fun x hx y hy => by grw [hf x y, edist_le_ediam_of_mem (mem_preimage.1 hx) hy]

/--
theorem `le_mul_ediam_image` / 定理 `le_mul_ediam_image`

English:
theorem le_mul_ediam_image
  given: (hf : AntilipschitzWith K f) (s : Set α)
  proof: (ediam_mono (subset_preimage_image _ _)).trans (hf.ediam_preimage_le (f '' s))

中文:
定理 le_mul_ediam_image
  条件: (hf : AntilipschitzWith K f) (s : Set α)
  证明: (ediam_mono (subset_preimage_image _ _)).trans (hf.ediam_preimage_le (f '' s))

Depends on / 依赖: ediam_mono, ediam_preimage_le, hf.ediam_preimage_le, subset_preimage_image
-/
theorem le_mul_ediam_image (hf : AntilipschitzWith K f) (s : Set α) :
    ediam s <= K * ediam (f '' s) :=
  (ediam_mono (subset_preimage_image _ _)).trans (hf.ediam_preimage_le (f '' s))

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: AntilipschitzWith 1 (id : α -> α)
  proof: fun x y => by
  simp only [ENNReal.coe_one, one_mul, id, le_refl]

中文:
定理 id
  结论: AntilipschitzWith 1 (id : α -> α)
  证明: fun x y => by
  simp only [ENNReal.coe_one, one_mul, id, le_refl]
-/
protected theorem id : AntilipschitzWith 1 (id : α -> α) := fun x y => by
  simp only [ENNReal.coe_one, one_mul, id, le_refl]

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {Kg : Real>=0} {g : β -> γ} (hg : AntilipschitzWith Kg g) {Kf : Real>=0} {f : α -> β}
  proof: fun x y =>
  calc
    edist x y <= Kf * edist (f x) (f y) := hf x y
    _ <= Kf * (Kg * edist (g (f x)) (g (f y))) := mul_right_mono (hg _ _)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]; rfl

中文:
定理 comp
  结论: {Kg : 实数>=0} {g : β -> γ} (hg : AntilipschitzWith Kg g) {Kf : 实数>=0} {f : α -> β}
  证明: fun x y =>
  calc
    edist x y <= Kf * edist (f x) (f y) := hf x y
    _ <= Kf * (Kg * edist (g (f x)) (g (f y))) := mul_right_mono (hg _ _)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]; rfl
-/
theorem comp {Kg : Real>=0} {g : β -> γ} (hg : AntilipschitzWith Kg g) {Kf : Real>=0} {f : α -> β}
    (hf : AntilipschitzWith Kf f) : AntilipschitzWith (Kf * Kg) (g ∘ f) := fun x y =>
  calc
    edist x y <= Kf * edist (f x) (f y) := hf x y
    _ <= Kf * (Kg * edist (g (f x)) (g (f y))) := mul_right_mono (hg _ _)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]; rfl

/--
theorem `domRestrict` / 定理 `domRestrict`

English:
theorem domRestrict
  given: (hf : AntilipschitzWith K f) (s : Set α)
  proof: fun x y => hf x y

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict

中文:
定理 domRestrict
  条件: (hf : AntilipschitzWith K f) (s : Set α)
  证明: fun x y => hf x y

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
-/
theorem domRestrict (hf : AntilipschitzWith K f) (s : Set α) :
    AntilipschitzWith K (s.domRestrict f) := fun x y => hf x y

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict

/--
theorem `codRestrict` / 定理 `codRestrict`

English:
theorem codRestrict
  given: (hf : AntilipschitzWith K f) {s : Set β} (hs : forall x, f x in s)
  proof: fun x y => hf x y

中文:
定理 codRestrict
  条件: (hf : AntilipschitzWith K f) {s : Set β} (hs : 对任意 x, f x in s)
  证明: fun x y => hf x y
-/
theorem codRestrict (hf : AntilipschitzWith K f) {s : Set β} (hs : forall x, f x in s) :
    AntilipschitzWith K (s.codRestrict f hs) := fun x y => hf x y

/--
theorem `to_rightInvOn'` / 定理 `to_rightInvOn'`

English:
theorem to_rightInvOn'
  statement: {s : Set α} (hf : AntilipschitzWith K (s.domRestrict f)) {g : β -> α}
  proof: fun x y => by
  simpa only [domRestrict_apply, g_inv x.mem, g_inv y.mem, Subtype.edist_mk_mk]
    using! hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩

中文:
定理 to_rightInvOn'
  结论: {s : Set α} (hf : AntilipschitzWith K (s.domRestrict f)) {g : β -> α}
  证明: fun x y => by
  simpa only [domRestrict_apply, g_inv x.mem, g_inv y.mem, Subtype.edist_mk_mk]
    using! hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩

Depends on / 依赖: Subtype, Subtype.edist_mk_mk, domRestrict_apply, edist_mk_mk, g_inv, g_maps, x.mem, y.mem
-/
theorem to_rightInvOn' {s : Set α} (hf : AntilipschitzWith K (s.domRestrict f)) {g : β -> α}
    {t : Set β} (g_maps : MapsTo g t s) (g_inv : RightInvOn g f t) :
    LipschitzWith K (t.domRestrict g) := fun x y => by
  simpa only [domRestrict_apply, g_inv x.mem, g_inv y.mem, Subtype.edist_mk_mk]
    using! hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩

/--
theorem `to_rightInvOn` / 定理 `to_rightInvOn`

English:
theorem to_rightInvOn
  given: (hf : AntilipschitzWith K f) {g : β -> α} {t : Set β} (h : RightInvOn g f t)
  proof: (hf.domRestrict univ).to_rightInvOn' (mapsTo_univ g t) h

中文:
定理 to_rightInvOn
  条件: (hf : AntilipschitzWith K f) {g : β -> α} {t : Set β} (h : RightInvOn g f t)
  证明: (hf.domRestrict univ).to_rightInvOn' (mapsTo_univ g t) h

Depends on / 依赖: domRestrict, hf.domRestrict, mapsTo_univ, to_rightInvOn
-/
theorem to_rightInvOn (hf : AntilipschitzWith K f) {g : β -> α} {t : Set β} (h : RightInvOn g f t) :
    LipschitzWith K (t.domRestrict g) := (hf.domRestrict univ).to_rightInvOn' (mapsTo_univ g t) h

/--
theorem `to_rightInverse` / 定理 `to_rightInverse`

English:
theorem to_rightInverse
  given: (hf : AntilipschitzWith K f) {g : β -> α} (hg : Function.RightInverse g f)
  proof: by
  intro x y
  have := hf (g x) (g y)
  rwa [hg x, hg y] at this

中文:
定理 to_rightInverse
  条件: (hf : AntilipschitzWith K f) {g : β -> α} (hg : Function.RightInverse g f)
  证明: by
  intro x y
  have := hf (g x) (g y)
  rwa [hg x, hg y] at this
-/
theorem to_rightInverse (hf : AntilipschitzWith K f) {g : β -> α} (hg : Function.RightInverse g f) :
    LipschitzWith K g := by
  intro x y
  have := hf (g x) (g y)
  rwa [hg x, hg y] at this

/--
theorem `comap_uniformity_le` / 定理 `comap_uniformity_le`

English:
theorem comap_uniformity_le
  given: (hf : AntilipschitzWith K f)
  statement: (𝓤 β).comap (Prod.map f f) <= 𝓤 α
  proof: by
  refine ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).2 fun ε h₀ => ?_
  refine ⟨(↑K)⁻¹ * ε, ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) h₀.ne', ?_⟩
  refine fun x hx => (hf x.1 x.2).trans_lt ?_
  rw [mul_comm]; rw [← div_eq_mul_inv] at hx
  rw [mul_comm]


中文:
定理 comap_uniformity_le
  条件: (hf : AntilipschitzWith K f)
  结论: (𝓤 β).comap (Prod.map f f) <= 𝓤 α
  证明: by
  refine ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).2 fun ε h₀ => ?_
  refine ⟨(↑K)⁻¹ * ε, ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) h₀.ne', ?_⟩
  refine fun x hx => (hf x.1 x.2).trans_lt ?_
  rw [mul_comm]; rw [← div_eq_mul_inv] at hx
  rw [mul_comm]


Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.inv_ne_zero, ENNReal.mul_lt_of_lt_div, ENNReal.mul_pos, coe_ne_top, div_eq_mul_inv, inv_ne_zero, le_basis_iff, mul_comm, mul_lt_of_lt_div, mul_pos, trans_lt, uniformity_basis_edist, uniformity_basis_edist.comap
-/
theorem comap_uniformity_le (hf : AntilipschitzWith K f) : (𝓤 β).comap (Prod.map f f) <= 𝓤 α := by
  refine ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).2 fun ε h₀ => ?_
  refine ⟨(↑K)⁻¹ * ε, ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) h₀.ne', ?_⟩
  refine fun x hx => (hf x.1 x.2).trans_lt ?_
  rw [mul_comm]; rw [← div_eq_mul_inv] at hx
  rw [mul_comm]
  exact ENNReal.mul_lt_of_lt_div hx

/--
theorem `isUniformInducing` / 定理 `isUniformInducing`

English:
theorem isUniformInducing
  given: (hf : AntilipschitzWith K f) (hfc : UniformContinuous f)
  proof: ⟨le_antisymm hf.comap_uniformity_le hfc.le_comap⟩

中文:
定理 isUniformInducing
  条件: (hf : AntilipschitzWith K f) (hfc : UniformContinuous f)
  证明: ⟨le_antisymm hf.comap_uniformity_le hfc.le_comap⟩

Depends on / 依赖: comap_uniformity_le, hf.comap_uniformity_le, hfc.le_comap, le_antisymm, le_comap
-/
theorem isUniformInducing (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    IsUniformInducing f :=
  ⟨le_antisymm hf.comap_uniformity_le hfc.le_comap⟩

/--
lemma `isUniformEmbedding` / 引理 `isUniformEmbedding`

English:
lemma isUniformEmbedding
  statement: {α β : Type*} [EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β}
  proof: ⟨hf.isUniformInducing hfc, hf.injective⟩

中文:
引理 isUniformEmbedding
  结论: {α β : 类型} [EMetricSpace α] [PseudoEMetricSpace β] {K : 实数>=0} {f : α -> β}
  证明: ⟨hf.isUniformInducing hfc, hf.injective⟩

Depends on / 依赖: hf.injective, hf.isUniformInducing, injective, isUniformInducing
-/
lemma isUniformEmbedding {α β : Type*} [EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β}
    (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) : IsUniformEmbedding f :=
  ⟨hf.isUniformInducing hfc, hf.injective⟩

/--
theorem `comap_nhds_le` / 定理 `comap_nhds_le`

English:
theorem comap_nhds_le
  given: (hf : AntilipschitzWith K f) (x : α)
  statement: (𝓝 (f x)).comap f <= 𝓝 x
  proof: by
  simp only [nhds_eq_comap_uniformity]
  grw [← hf.comap_uniformity_le]
  simp [comap_comap, Function.comp_def]

中文:
定理 comap_nhds_le
  条件: (hf : AntilipschitzWith K f) (x : α)
  结论: (𝓝 (f x)).comap f <= 𝓝 x
  证明: by
  simp only [nhds_eq_comap_uniformity]
  grw [← hf.comap_uniformity_le]
  simp [comap_comap, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comap_comap, comap_uniformity_le, comp_def, hf.comap_uniformity_le, nhds_eq_comap_uniformity
-/
theorem comap_nhds_le (hf : AntilipschitzWith K f) (x : α) : (𝓝 (f x)).comap f <= 𝓝 x := by
  simp only [nhds_eq_comap_uniformity]
  grw [← hf.comap_uniformity_le]
  simp [comap_comap, Function.comp_def]

/--
theorem `isInducing` / 定理 `isInducing`

English:
theorem isInducing
  given: (hf : AntilipschitzWith K f) (hfc : Continuous f)
  statement: IsInducing f
  proof: isInducing_iff_nhds.mpr fun x => le_antisymm (hfc.tendsto x).le_comap hf.comap_nhds_le _

中文:
定理 isInducing
  条件: (hf : AntilipschitzWith K f) (hfc : Continuous f)
  结论: IsInducing f
  证明: isInducing_iff_nhds.mpr fun x => le_antisymm (hfc.tendsto x).le_comap hf.comap_nhds_le _

Depends on / 依赖: comap_nhds_le, hf.comap_nhds_le, hfc.tendsto, isInducing_iff_nhds, isInducing_iff_nhds.mpr, le_antisymm, le_comap, tendsto
-/
theorem isInducing (hf : AntilipschitzWith K f) (hfc : Continuous f) : IsInducing f :=
isInducing_iff_nhds.mpr fun x => le_antisymm (hfc.tendsto x).le_comap hf.comap_nhds_le _

/--
lemma `isEmbedding` / 引理 `isEmbedding`

English:
lemma isEmbedding
  statement: {α β : Type*} [EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β}
  proof: .isEmbedding hf.isInducing hfc

中文:
引理 isEmbedding
  结论: {α β : 类型} [EMetricSpace α] [PseudoEMetricSpace β] {K : 实数>=0} {f : α -> β}
  证明: .isEmbedding hf.isInducing hfc

Depends on / 依赖: hf.isInducing, isEmbedding, isInducing
-/
lemma isEmbedding {α β : Type*} [EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β}
    (hf : AntilipschitzWith K f) (hfc : Continuous f) : IsEmbedding f :=
.isEmbedding hf.isInducing hfc

/--
theorem `isComplete_range` / 定理 `isComplete_range`

English:
theorem isComplete_range
  statement: [CompleteSpace α] (hf : AntilipschitzWith K f)
  proof: (hf.isUniformInducing hfc).isComplete_range

中文:
定理 isComplete_range
  结论: [CompleteSpace α] (hf : AntilipschitzWith K f)
  证明: (hf.isUniformInducing hfc).isComplete_range

Depends on / 依赖: hf.isUniformInducing, isComplete_range, isUniformInducing
-/
theorem isComplete_range [CompleteSpace α] (hf : AntilipschitzWith K f)
    (hfc : UniformContinuous f) : IsComplete (range f) :=
  (hf.isUniformInducing hfc).isComplete_range

/--
theorem `isClosed_range` / 定理 `isClosed_range`

English:
theorem isClosed_range
  statement: {α β : Type*} [PseudoEMetricSpace α] [EMetricSpace β] [CompleteSpace α]
  proof: (hf.isComplete_range hfc).isClosed

中文:
定理 isClosed_range
  结论: {α β : 类型} [PseudoEMetricSpace α] [EMetricSpace β] [CompleteSpace α]
  证明: (hf.isComplete_range hfc).isClosed

Depends on / 依赖: hf.isComplete_range, isClosed, isComplete_range
-/
theorem isClosed_range {α β : Type*} [PseudoEMetricSpace α] [EMetricSpace β] [CompleteSpace α]
    {f : α -> β} {K : Real>=0} (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    IsClosed (range f) :=
  (hf.isComplete_range hfc).isClosed

/--
theorem `isClosedEmbedding` / 定理 `isClosedEmbedding`

English:
theorem isClosedEmbedding
  statement: {α : Type*} {β : Type*} [EMetricSpace α] [EMetricSpace β] {K : Real>=0}
  proof: { (hf.isUniformEmbedding hfc).isEmbedding with isClosed_range := hf.isClosed_range hfc }

中文:
定理 isClosedEmbedding
  结论: {α : 类型} {β : 类型} [EMetricSpace α] [EMetricSpace β] {K : 实数>=0}
  证明: { (hf.isUniformEmbedding hfc).isEmbedding with isClosed_range := hf.isClosed_range hfc }

Depends on / 依赖: hf.isClosed_range, hf.isUniformEmbedding, isClosed_range, isEmbedding, isUniformEmbedding
-/
theorem isClosedEmbedding {α : Type*} {β : Type*} [EMetricSpace α] [EMetricSpace β] {K : Real>=0}
    {f : α -> β} [CompleteSpace α] (hf : AntilipschitzWith K f) (hfc : UniformContinuous f) :
    IsClosedEmbedding f :=
  { (hf.isUniformEmbedding hfc).isEmbedding with isClosed_range := hf.isClosed_range hfc }

/--
theorem `subtype_coe` / 定理 `subtype_coe`

English:
theorem subtype_coe
  given: (s : Set α)
  statement: AntilipschitzWith 1 ((↑) : s -> α)
  proof: AntilipschitzWith.id.domRestrict s

@[nontriviality]

中文:
定理 subtype_coe
  条件: (s : Set α)
  结论: AntilipschitzWith 1 ((↑) : s -> α)
  证明: AntilipschitzWith.id.domRestrict s

@[nontriviality]

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.id.domRestrict, domRestrict
-/
theorem subtype_coe (s : Set α) : AntilipschitzWith 1 ((↑) : s -> α) :=
  AntilipschitzWith.id.domRestrict s

@[nontriviality]
/--
theorem `of_subsingleton` / 定理 `of_subsingleton`

English:
theorem of_subsingleton
  given: [Subsingleton α] {K : Real>=0}
  statement: AntilipschitzWith K f
  proof: fun x y => by
  simp only [Subsingleton.elim x y, edist_self, zero_le]

中文:
定理 of_subsingleton
  条件: [Subsingleton α] {K : 实数>=0}
  结论: AntilipschitzWith K f
  证明: fun x y => by
  simp only [Subsingleton.elim x y, edist_self, zero_le]

Depends on / 依赖: Subsingleton, Subsingleton.elim, edist_self, zero_le
-/
theorem of_subsingleton [Subsingleton α] {K : Real>=0} : AntilipschitzWith K f := fun x y => by
  simp only [Subsingleton.elim x y, edist_self, zero_le]

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  statement: {α β} [EMetricSpace α] [PseudoEMetricSpace β] {f : α -> β}
  proof: ⟨fun x y => edist_le_zero.1 (h x y).trans_eq zero_mul _⟩

中文:
定理 subsingleton
  结论: {α β} [EMetricSpace α] [PseudoEMetricSpace β] {f : α -> β}
  证明: ⟨fun x y => edist_le_zero.1 (h x y).trans_eq zero_mul _⟩
-/
protected theorem subsingleton {α β} [EMetricSpace α] [PseudoEMetricSpace β] {f : α -> β}
    (h : AntilipschitzWith 0 f) : Subsingleton α :=
⟨fun x y => edist_le_zero.1 (h x y).trans_eq zero_mul _⟩

/--
theorem `pos` / 定理 `pos`

English:
theorem pos
  statement: {α} [EMetricSpace α] [Nontrivial α] {f : α -> β}
  proof: by
  by_contra! h₀
  obtain rfl : K = 0 := by rwa [le_zero_iff] at h₀
  exact not_subsingleton α hf.subsingleton

中文:
定理 pos
  结论: {α} [EMetricSpace α] [Nontrivial α] {f : α -> β}
  证明: by
  by_contra! h₀
  obtain rfl : K = 0 := by rwa [le_zero_iff] at h₀
  exact not_subsingleton α hf.subsingleton
-/
protected theorem pos {α} [EMetricSpace α] [Nontrivial α] {f : α -> β}
    (hf : AntilipschitzWith K f) : 0 < K := by
  by_contra! h₀
  obtain rfl : K = 0 := by rwa [le_zero_iff] at h₀
  exact not_subsingleton α hf.subsingleton

end AntilipschitzWith

namespace AntilipschitzWith

open Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {K : Real>=0} {f : α -> β}

/--
theorem `isBounded_preimage` / 定理 `isBounded_preimage`

English:
theorem isBounded_preimage
  given: (hf : AntilipschitzWith K f) {s : Set β} (hs : IsBounded s)
  proof: isBounded_iff_ediam_ne_top.2 ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top) (hf.ediam_preimage_le _)

中文:
定理 isBounded_preimage
  条件: (hf : AntilipschitzWith K f) {s : Set β} (hs : IsBounded s)
  证明: isBounded_iff_ediam_ne_top.2 ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top) (hf.ediam_preimage_le _)

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.mul_ne_top, coe_ne_top, ediam_ne_top, ediam_preimage_le, hf.ediam_preimage_le, hs.ediam_ne_top, isBounded_iff_ediam_ne_top, mul_ne_top, ne_top_of_le_ne_top
-/
theorem isBounded_preimage (hf : AntilipschitzWith K f) {s : Set β} (hs : IsBounded s) :
    IsBounded (f ⁻¹' s) :=
isBounded_iff_ediam_ne_top.2 ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top) (hf.ediam_preimage_le _)

/--
theorem `tendsto_cobounded` / 定理 `tendsto_cobounded`

English:
theorem tendsto_cobounded
  given: (hf : AntilipschitzWith K f)
  statement: Tendsto f (cobounded α) (cobounded β)
  proof: compl_surjective.forall.2 fun _ => hf.isBounded_preimage

中文:
定理 tendsto_cobounded
  条件: (hf : AntilipschitzWith K f)
  结论: Tendsto f (cobounded α) (cobounded β)
  证明: compl_surjective.forall.2 fun _ => hf.isBounded_preimage

Depends on / 依赖: compl_surjective, compl_surjective.forall, hf.isBounded_preimage, isBounded_preimage
-/
theorem tendsto_cobounded (hf : AntilipschitzWith K f) : Tendsto f (cobounded α) (cobounded β) :=
  compl_surjective.forall.2 fun _ => hf.isBounded_preimage

/--
theorem `properSpace` / 定理 `properSpace`

English:
theorem properSpace
  statement: {α : Type*} [MetricSpace α] {K : Real>=0} {f : α -> β} [ProperSpace α]
  proof: by
  refine ⟨fun x₀ r => ?_⟩
  let K := f ⁻¹' closedBall x₀ r
  have A : IsClosed K := isClosed_closedBall.preimage f_cont
  have B : IsBounded K := hK.isBounded_preimage isBounded_closedBall
  have : IsCompact K := isCompact_iff_isClosed_bounded.2 ⟨A, B⟩
  convert! this.image f_cont
  exact (hf.ima

中文:
定理 properSpace
  结论: {α : 类型} [MetricSpace α] {K : 实数>=0} {f : α -> β} [命题erSpace α]
  证明: by
  refine ⟨fun x₀ r => ?_⟩
  let K := f ⁻¹' closedBall x₀ r
  have A : IsClosed K := isClosed_closedBall.preimage f_cont
  have B : IsBounded K := hK.isBounded_preimage isBounded_closedBall
  have : IsCompact K := isCompact_iff_isClosed_bounded.2 ⟨A, B⟩
  convert! this.image f_cont
  exact (hf.ima
-/
protected theorem properSpace {α : Type*} [MetricSpace α] {K : Real>=0} {f : α -> β} [ProperSpace α]
    (hK : AntilipschitzWith K f) (f_cont : Continuous f) (hf : Function.Surjective f) :
    ProperSpace β := by
  refine ⟨fun x₀ r => ?_⟩
  let K := f ⁻¹' closedBall x₀ r
  have A : IsClosed K := isClosed_closedBall.preimage f_cont
  have B : IsBounded K := hK.isBounded_preimage isBounded_closedBall
  have : IsCompact K := isCompact_iff_isClosed_bounded.2 ⟨A, B⟩
  convert! this.image f_cont
  exact (hf.image_preimage _).symm

/--
theorem `isBounded_of_image2_left` / 定理 `isBounded_of_image2_left`

English:
theorem isBounded_of_image2_left
  statement: (f : α -> β -> γ) {K₁ : Real>=0}
  proof: by
  contrapose! hst
  obtain ⟨b, hb⟩ : t.Nonempty := nonempty_of_not_isBounded hst.2
  have : ¬IsBounded (Set.image2 f s {b}) := by
    intro h
    apply hst.1
    rw [Set.image2_singleton_right] at h
    replace h := (hf b).isBounded_preimage h
    exact h.subset (subset_preimage_image _ _)
  exac

中文:
定理 isBounded_of_image2_left
  结论: (f : α -> β -> γ) {K₁ : 实数>=0}
  证明: by
  contrapose! hst
  obtain ⟨b, hb⟩ : t.Nonempty := nonempty_of_not_isBounded hst.2
  have : ¬IsBounded (Set.image2 f s {b}) := by
    intro h
    apply hst.1
    rw [Set.image2_singleton_right] at h
    replace h := (hf b).isBounded_preimage h
    exact h.subset (subset_preimage_image _ _)
  exac

Depends on / 依赖: IsBounded, IsBounded.subset, Nonempty, Set.image2, Set.image2_singleton_right, contrapose, h.subset, image2, image2_singleton_right, image2_subset, isBounded_preimage, nonempty_of_not_isBounded, replace, singleton_subset_iff, singleton_subset_iff.mpr, subset, subset_preimage_image, subset_rfl, t.Nonempty
-/
theorem isBounded_of_image2_left (f : α -> β -> γ) {K₁ : Real>=0}
    (hf : forall b, AntilipschitzWith K₁ fun a => f a b) {s : Set α} {t : Set β}
    (hst : IsBounded (Set.image2 f s t)) : IsBounded s ∨ IsBounded t := by
  contrapose! hst
  obtain ⟨b, hb⟩ : t.Nonempty := nonempty_of_not_isBounded hst.2
  have : ¬IsBounded (Set.image2 f s {b}) := by
    intro h
    apply hst.1
    rw [Set.image2_singleton_right] at h
    replace h := (hf b).isBounded_preimage h
    exact h.subset (subset_preimage_image _ _)
  exact mt (IsBounded.subset · (image2_subset subset_rfl (singleton_subset_iff.mpr hb))) this

/--
theorem `isBounded_of_image2_right` / 定理 `isBounded_of_image2_right`

English:
theorem isBounded_of_image2_right
  statement: {f : α -> β -> γ} {K₂ : Real>=0} (hf : forall a, AntilipschitzWith K₂ (f a))
  proof: Or.symm isBounded_of_image2_left (flip f) hf image2_swap f s t ▸ hst

中文:
定理 isBounded_of_image2_right
  结论: {f : α -> β -> γ} {K₂ : 实数>=0} (hf : 对任意 a, AntilipschitzWith K₂ (f a))
  证明: Or.symm isBounded_of_image2_left (flip f) hf image2_swap f s t ▸ hst

Depends on / 依赖: Or.symm, image2_swap, isBounded_of_image2_left
-/
theorem isBounded_of_image2_right {f : α -> β -> γ} {K₂ : Real>=0} (hf : forall a, AntilipschitzWith K₂ (f a))
    {s : Set α} {t : Set β} (hst : IsBounded (Set.image2 f s t)) : IsBounded s ∨ IsBounded t :=
Or.symm isBounded_of_image2_left (flip f) hf image2_swap f s t ▸ hst

end AntilipschitzWith

/--
theorem `LipschitzWith.to_rightInverse` / 定理 `LipschitzWith.to_rightInverse`

English:
theorem LipschitzWith.to_rightInverse
  statement: [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0}
  proof: fun x y => by simpa only [hg _] using hf (g x) (g y)

中文:
定理 LipschitzWith.to_rightInverse
  结论: [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : 实数>=0}
  证明: fun x y => by simpa only [hg _] using hf (g x) (g y)
-/
theorem LipschitzWith.to_rightInverse [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0}
    {f : α -> β} (hf : LipschitzWith K f) {g : β -> α} (hg : Function.RightInverse g f) :
    AntilipschitzWith K g := fun x y => by simpa only [hg _] using hf (g x) (g y)
