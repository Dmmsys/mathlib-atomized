/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Uniform convergence

A sequence of functions `Fₙ` (with values in a metric space) converges uniformly on a set `s` to a
function `f` if, for all `ε > 0`, for all large enough `n`, one has for all `y ∈ s` the inequality
`dist (f y, Fₙ y) < ε`. Under uniform convergence, many properties of the `Fₙ` pass to the limit,
most notably continuity. We prove this in the file, defining the notion of uniform convergence
in the more general setting of uniform spaces, and with respect to an arbitrary indexing set
endowed with a filter (instead of just `ℕ` with `atTop`).

## Main results

Let `α` be a topological space, `β` a uniform space, `Fₙ` and `f` be functions from `α` to `β`
(where the index `n` belongs to an indexing type `ι` endowed with a filter `p`).

* `TendstoUniformlyOn F f p s`: the fact that `Fₙ` converges uniformly to `f` on `s`. This means
  that, for any entourage `u` of the diagonal, for large enough `n` (with respect to `p`), one has
  `(f y, Fₙ y) ∈ u` for all `y ∈ s`.
* `TendstoUniformly F f p`: same notion with `s = univ`.
* `TendstoUniformlyOn.continuousOn`: a uniform limit on a set of functions which are continuous
  on this set is itself continuous on this set.
* `TendstoUniformly.continuous`: a uniform limit of continuous functions is continuous.
* `TendstoUniformlyOn.tendsto_comp`: If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends
  to `x` within `s`, then `Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s`.
* `TendstoUniformly.tendsto_comp`: If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then
  `Fₙ gₙ` tends to `f x`.

Finally, we introduce the notion of a uniform Cauchy sequence, which is to uniform
convergence what a Cauchy sequence is to the usual notion of convergence.

## Implementation notes

We derive most of our initial results from an auxiliary definition `TendstoUniformlyOnFilter`.
This definition in and of itself can sometimes be useful, e.g., when studying the local behavior
of the `Fₙ` near a point, which would typically look like `TendstoUniformlyOnFilter F f p (𝓝 x)`.
Still, while this may be the "correct" definition (see
`tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`), it is somewhat unwieldy to work with in
practice. Thus, we provide the more traditional definition in `TendstoUniformlyOn`.

## Tags

Uniform limit, uniform convergence, tends uniformly to
-/

@[expose] public section

noncomputable section

open Topology Uniformity Filter Set Uniform

variable {α β γ ι : Type*} [UniformSpace β]
variable {F : ι -> α -> β} {f : α -> β} {s s' : Set α} {x : α} {p : Filter ι} {p' : Filter α}

/-!
### Different notions of uniform convergence

We define uniform convergence, on a set or in the whole space.
-/

/--
Definition of `TendstoUniformlyOnFilter` / `TendstoUniformlyOnFilter` 的定义

English:
definition TendstoUniformlyOnFilter
  signature: (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (p' : Filter α)
  body: forall u in 𝓤 β, forallᶠ n : ι × α in p ×ˢ p', (f n.snd, F n.fst n.snd) in u

中文:
定义 TendstoUniformlyOnFilter
  签名: (F : ι -> α -> β) (f : α -> β) (p : 滤子 ι) (p' : 滤子 α)
  定义体: forall u in 𝓤 β, forallᶠ n : ι × α in p ×ˢ p', (f n.snd, F n.fst n.snd) in u

Depends on / 依赖: n.fst, n.snd
-/
def TendstoUniformlyOnFilter (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (p' : Filter α) :=
  forall u in 𝓤 β, forallᶠ n : ι × α in p ×ˢ p', (f n.snd, F n.fst n.snd) in u

/--
theorem `tendstoUniformlyOnFilter_iff_tendsto` / 定理 `tendstoUniformlyOnFilter_iff_tendsto`

English:
theorem tendstoUniformlyOnFilter_iff_tendsto
  proof: Iff.rfl

中文:
定理 tendstoUniformlyOnFilter_iff_tendsto
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem tendstoUniformlyOnFilter_iff_tendsto :
    TendstoUniformlyOnFilter F f p p' ↔
      Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ p') (𝓤 β) :=
  Iff.rfl

/--
Definition of `TendstoUniformlyOn` / `TendstoUniformlyOn` 的定义

English:
definition TendstoUniformlyOn
  signature: (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (s : Set α)
  body: forall u in 𝓤 β, forallᶠ n in p, forall x : α, x in s -> (f x, F n x) in u

中文:
定义 TendstoUniformlyOn
  签名: (F : ι -> α -> β) (f : α -> β) (p : 滤子 ι) (s : 集合 α)
  定义体: forall u in 𝓤 β, forallᶠ n in p, forall x : α, x in s -> (f x, F n x) in u
-/
def TendstoUniformlyOn (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (s : Set α) :=
  forall u in 𝓤 β, forallᶠ n in p, forall x : α, x in s -> (f x, F n x) in u

/--
theorem `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter` / 定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`

English:
theorem tendstoUniformlyOn_iff_tendstoUniformlyOnFilter
  proof: by
  simp only [TendstoUniformlyOn, TendstoUniformlyOnFilter]
  apply forall₂_congr
  simp_rw [eventually_prod_principal_iff]
  simp

alias ⟨TendstoUniformlyOn.tendstoUniformlyOnFilter, TendstoUniformlyOnFilter.tendstoUniformlyOn⟩ :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter

中文:
定理 tendstoUniformlyOn_iff_tendstoUniformlyOnFilter
  证明: by
  simp only [TendstoUniformlyOn, TendstoUniformlyOnFilter]
  apply forall₂_congr
  simp_rw [eventually_prod_principal_iff]
  simp

alias ⟨TendstoUniformlyOn.tendstoUniformlyOnFilter, TendstoUniformlyOnFilter.tendstoUniformlyOn⟩ :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter

Depends on / 依赖: TendstoUniformlyOn, TendstoUniformlyOnFilter, eventually_prod_principal_iff, simp_rw
-/
theorem tendstoUniformlyOn_iff_tendstoUniformlyOnFilter :
    TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter F f p (𝓟 s) := by
  simp only [TendstoUniformlyOn, TendstoUniformlyOnFilter]
  apply forall₂_congr
  simp_rw [eventually_prod_principal_iff]
  simp

alias ⟨TendstoUniformlyOn.tendstoUniformlyOnFilter, TendstoUniformlyOnFilter.tendstoUniformlyOn⟩ :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter

/--
theorem `tendstoUniformlyOn_iff_tendsto` / 定理 `tendstoUniformlyOn_iff_tendsto`

English:
theorem tendstoUniformlyOn_iff_tendsto
  proof: by
  simp [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

中文:
定理 tendstoUniformlyOn_iff_tendsto
  证明: by
  simp [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

Depends on / 依赖: tendstoUniformlyOnFilter_iff_tendsto, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter
-/
theorem tendstoUniformlyOn_iff_tendsto :
    TendstoUniformlyOn F f p s ↔
    Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) (𝓤 β) := by
  simp [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` with respect to a
filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x`. -/
@[wikidata Q1411887]
/--
Definition of `TendstoUniformly` / `TendstoUniformly` 的定义

English:
definition TendstoUniformly
  signature: (F : ι -> α -> β) (f : α -> β) (p : Filter ι)
  body: forall u in 𝓤 β, forallᶠ n in p, forall x : α, (f x, F n x) in u

中文:
定义 TendstoUniformly
  签名: (F : ι -> α -> β) (f : α -> β) (p : 滤子 ι)
  定义体: forall u in 𝓤 β, forallᶠ n in p, forall x : α, (f x, F n x) in u
-/
def TendstoUniformly (F : ι -> α -> β) (f : α -> β) (p : Filter ι) :=
  forall u in 𝓤 β, forallᶠ n in p, forall x : α, (f x, F n x) in u

/--
theorem `tendstoUniformlyOn_univ` / 定理 `tendstoUniformlyOn_univ`

English:
theorem tendstoUniformlyOn_univ
  statement: TendstoUniformlyOn F f p univ ↔ TendstoUniformly F f p
  proof: by
  simp [TendstoUniformlyOn, TendstoUniformly]

中文:
定理 tendstoUniformlyOn_univ
  结论: TendstoUniformlyOn F f p univ ↔ TendstoUniformly F f p
  证明: by
  simp [TendstoUniformlyOn, TendstoUniformly]

Depends on / 依赖: TendstoUniformly, TendstoUniformlyOn
-/
theorem tendstoUniformlyOn_univ : TendstoUniformlyOn F f p univ ↔ TendstoUniformly F f p := by
  simp [TendstoUniformlyOn, TendstoUniformly]

/--
theorem `tendstoUniformly_iff_tendstoUniformlyOnFilter` / 定理 `tendstoUniformly_iff_tendstoUniformlyOnFilter`

English:
theorem tendstoUniformly_iff_tendstoUniformlyOnFilter
  proof: by
  rw [← tendstoUniformlyOn_univ]; rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]; rw [principal_univ]

中文:
定理 tendstoUniformly_iff_tendstoUniformlyOnFilter
  证明: by
  rw [← tendstoUniformlyOn_univ]; rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]; rw [principal_univ]

Depends on / 依赖: principal_univ, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOn_univ
-/
theorem tendstoUniformly_iff_tendstoUniformlyOnFilter :
    TendstoUniformly F f p ↔ TendstoUniformlyOnFilter F f p ⊤ := by
  rw [← tendstoUniformlyOn_univ]; rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]; rw [principal_univ]

/--
theorem `TendstoUniformly.tendstoUniformlyOnFilter` / 定理 `TendstoUniformly.tendstoUniformlyOnFilter`

English:
theorem TendstoUniformly.tendstoUniformlyOnFilter
  given: (h : TendstoUniformly F f p)
  proof: by rwa [← tendstoUniformly_iff_tendstoUniformlyOnFilter]

中文:
定理 TendstoUniformly.tendstoUniformlyOnFilter
  条件: (h : TendstoUniformly F f p)
  证明: by rwa [← tendstoUniformly_iff_tendstoUniformlyOnFilter]

Depends on / 依赖: tendstoUniformly_iff_tendstoUniformlyOnFilter
-/
theorem TendstoUniformly.tendstoUniformlyOnFilter (h : TendstoUniformly F f p) :
    TendstoUniformlyOnFilter F f p ⊤ := by rwa [← tendstoUniformly_iff_tendstoUniformlyOnFilter]

/--
theorem `tendstoUniformlyOn_iff_tendstoUniformly_comp_coe` / 定理 `tendstoUniformlyOn_iff_tendstoUniformly_comp_coe`

English:
theorem tendstoUniformlyOn_iff_tendstoUniformly_comp_coe
  proof: forall₂_congr fun u _ => by simp

中文:
定理 tendstoUniformlyOn_iff_tendstoUniformly_comp_coe
  证明: forall₂_congr fun u _ => by simp
-/
theorem tendstoUniformlyOn_iff_tendstoUniformly_comp_coe :
    TendstoUniformlyOn F f p s ↔ TendstoUniformly (fun i (x : s) => F i x) (f ∘ (↑)) p :=
  forall₂_congr fun u _ => by simp

/--
lemma `tendstoUniformlyOn_iff_restrict` / 引理 `tendstoUniformlyOn_iff_restrict`

English:
lemma tendstoUniformlyOn_iff_restrict
  given: {K : Set α}
  statement: TendstoUniformlyOn F f p K ↔
  proof: tendstoUniformlyOn_iff_tendstoUniformly_comp_coe

中文:
引理 tendstoUniformlyOn_iff_restrict
  条件: {K : 集合 α}
  结论: TendstoUniformlyOn F f p K ↔
  证明: tendstoUniformlyOn_iff_tendstoUniformly_comp_coe

Depends on / 依赖: tendstoUniformlyOn_iff_tendstoUniformly_comp_coe
-/
lemma tendstoUniformlyOn_iff_restrict {K : Set α} : TendstoUniformlyOn F f p K ↔
    TendstoUniformly (fun n : ι => K.domRestrict (F n)) (K.domRestrict f) p :=
  tendstoUniformlyOn_iff_tendstoUniformly_comp_coe

/--
theorem `tendstoUniformly_iff_tendsto` / 定理 `tendstoUniformly_iff_tendsto`

English:
theorem tendstoUniformly_iff_tendsto
  proof: by
  simp [tendstoUniformly_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

中文:
定理 tendstoUniformly_iff_tendsto
  证明: by
  simp [tendstoUniformly_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

Depends on / 依赖: tendstoUniformlyOnFilter_iff_tendsto, tendstoUniformly_iff_tendstoUniformlyOnFilter
-/
theorem tendstoUniformly_iff_tendsto :
    TendstoUniformly F f p ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ ⊤) (𝓤 β) := by
  simp [tendstoUniformly_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

/--
theorem `TendstoUniformlyOnFilter.tendsto_at` / 定理 `TendstoUniformlyOnFilter.tendsto_at`

English:
theorem TendstoUniformlyOnFilter.tendsto_at
  statement: (h : TendstoUniformlyOnFilter F f p p')
  proof: by
  refine Uniform.tendsto_nhds_right.mpr fun u hu => mem_map.mpr ?_
  filter_upwards [(h u hu).curry]
  intro i h
  simpa using h.filter_mono hx

中文:
定理 TendstoUniformlyOnFilter.tendsto_at
  结论: (h : TendstoUniformlyOnFilter F f p p')
  证明: by
  refine Uniform.tendsto_nhds_right.mpr fun u hu => mem_map.mpr ?_
  filter_upwards [(h u hu).curry]
  intro i h
  simpa using h.filter_mono hx

Depends on / 依赖: Uniform, Uniform.tendsto_nhds_right.mpr, filter_mono, filter_upwards, h.filter_mono, mem_map, mem_map.mpr, tendsto_nhds_right
-/
theorem TendstoUniformlyOnFilter.tendsto_at (h : TendstoUniformlyOnFilter F f p p')
(hx : 𝓟 {x} <= p') : Tendsto (fun n => F n x) p 𝓝 (f x) := by
  refine Uniform.tendsto_nhds_right.mpr fun u hu => mem_map.mpr ?_
  filter_upwards [(h u hu).curry]
  intro i h
  simpa using h.filter_mono hx

/--
theorem `TendstoUniformlyOn.tendsto_at` / 定理 `TendstoUniformlyOn.tendsto_at`

English:
theorem TendstoUniformlyOn.tendsto_at
  given: (h : TendstoUniformlyOn F f p s) (hx : x in s)
  proof: h.tendstoUniformlyOnFilter.tendsto_at
    (le_principal_iff.mpr <| mem_principal.mpr <| singleton_subset_iff.mpr <| hx)

中文:
定理 TendstoUniformlyOn.tendsto_at
  条件: (h : TendstoUniformlyOn F f p s) (hx : x in s)
  证明: h.tendstoUniformlyOnFilter.tendsto_at
    (le_principal_iff.mpr <| mem_principal.mpr <| singleton_subset_iff.mpr <| hx)

Depends on / 依赖: h.tendstoUniformlyOnFilter.tendsto_at, le_principal_iff, le_principal_iff.mpr, mem_principal, mem_principal.mpr, singleton_subset_iff, singleton_subset_iff.mpr, tendstoUniformlyOnFilter, tendsto_at
-/
theorem TendstoUniformlyOn.tendsto_at (h : TendstoUniformlyOn F f p s) (hx : x in s) :
Tendsto (fun n => F n x) p 𝓝 (f x) :=
  h.tendstoUniformlyOnFilter.tendsto_at
    (le_principal_iff.mpr <| mem_principal.mpr <| singleton_subset_iff.mpr <| hx)

/--
theorem `TendstoUniformly.tendsto_at` / 定理 `TendstoUniformly.tendsto_at`

English:
theorem TendstoUniformly.tendsto_at
  given: (h : TendstoUniformly F f p) (x : α)
  proof: h.tendstoUniformlyOnFilter.tendsto_at le_top

中文:
定理 TendstoUniformly.tendsto_at
  条件: (h : TendstoUniformly F f p) (x : α)
  证明: h.tendstoUniformlyOnFilter.tendsto_at le_top

Depends on / 依赖: h.tendstoUniformlyOnFilter.tendsto_at, le_top, tendstoUniformlyOnFilter, tendsto_at
-/
theorem TendstoUniformly.tendsto_at (h : TendstoUniformly F f p) (x : α) :
Tendsto (fun n => F n x) p 𝓝 (f x) :=
  h.tendstoUniformlyOnFilter.tendsto_at le_top

/--
theorem `TendstoUniformlyOnFilter.mono_left` / 定理 `TendstoUniformlyOnFilter.mono_left`

English:
theorem TendstoUniformlyOnFilter.mono_left
  statement: {p'' : Filter ι} (h : TendstoUniformlyOnFilter F f p p')
  proof: fun u hu =>
  (h u hu).filter_mono (p'.prod_mono_left hp)

中文:
定理 TendstoUniformlyOnFilter.mono_left
  结论: {p'' : 滤子 ι} (h : TendstoUniformlyOnFilter F f p p')
  证明: fun u hu =>
  (h u hu).filter_mono (p'.prod_mono_left hp)
-/
theorem TendstoUniformlyOnFilter.mono_left {p'' : Filter ι} (h : TendstoUniformlyOnFilter F f p p')
    (hp : p'' <= p) : TendstoUniformlyOnFilter F f p'' p' := fun u hu =>
  (h u hu).filter_mono (p'.prod_mono_left hp)

/--
theorem `TendstoUniformlyOnFilter.mono_right` / 定理 `TendstoUniformlyOnFilter.mono_right`

English:
theorem TendstoUniformlyOnFilter.mono_right
  statement: {p'' : Filter α} (h : TendstoUniformlyOnFilter F f p p')
  proof: fun u hu =>
  (h u hu).filter_mono (p.prod_mono_right hp)

中文:
定理 TendstoUniformlyOnFilter.mono_right
  结论: {p'' : 滤子 α} (h : TendstoUniformlyOnFilter F f p p')
  证明: fun u hu =>
  (h u hu).filter_mono (p.prod_mono_right hp)
-/
theorem TendstoUniformlyOnFilter.mono_right {p'' : Filter α} (h : TendstoUniformlyOnFilter F f p p')
    (hp : p'' <= p') : TendstoUniformlyOnFilter F f p p'' := fun u hu =>
  (h u hu).filter_mono (p.prod_mono_right hp)

/--
theorem `TendstoUniformlyOn.mono` / 定理 `TendstoUniformlyOn.mono`

English:
theorem TendstoUniformlyOn.mono
  given: (h : TendstoUniformlyOn F f p s) (h' : s' subseteq s)
  proof: tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (h.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr <| mem_principal.mpr h'))

中文:
定理 TendstoUniformlyOn.mono
  条件: (h : TendstoUniformlyOn F f p s) (h' : s' subseteq s)
  证明: tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (h.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr <| mem_principal.mpr h'))

Depends on / 依赖: h.tendstoUniformlyOnFilter.mono_right, le_principal_iff, le_principal_iff.mpr, mem_principal, mem_principal.mpr, mono_right, tendstoUniformlyOnFilter, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
-/
theorem TendstoUniformlyOn.mono (h : TendstoUniformlyOn F f p s) (h' : s' subseteq s) :
    TendstoUniformlyOn F f p s' :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (h.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr <| mem_principal.mpr h'))

/--
theorem `TendstoUniformlyOnFilter.congr_inseparable` / 定理 `TendstoUniformlyOnFilter.congr_inseparable`

English:
theorem TendstoUniformlyOnFilter.congr_inseparable
  statement: {F' : ι -> α -> β}
  proof: by
  rw [tendstoUniformlyOnFilter_iff_tendsto]; rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact fun i hi => (hf i hi).congr (hff'.mono fun x hx =>
    (Inseparable.rfl.prod hx).mem_open_iff hi.2)

中文:
定理 TendstoUniformlyOnFilter.congr_inseparable
  结论: {F' : ι -> α -> β}
  证明: by
  rw [tendstoUniformlyOnFilter_iff_tendsto]; rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact fun i hi => (hf i hi).congr (hff'.mono fun x hx =>
    (Inseparable.rfl.prod hx).mem_open_iff hi.2)

Depends on / 依赖: Inseparable, Inseparable.rfl.prod, mem_open_iff, tendstoUniformlyOnFilter_iff_tendsto, tendsto_right_iff, uniformity_hasBasis_open, uniformity_hasBasis_open.tendsto_right_iff
-/
theorem TendstoUniformlyOnFilter.congr_inseparable {F' : ι -> α -> β}
    (hf : TendstoUniformlyOnFilter F f p p')
    (hff' : forallᶠ n : ι × α in p ×ˢ p', Inseparable (F n.fst n.snd) (F' n.fst n.snd)) :
    TendstoUniformlyOnFilter F' f p p' := by
  rw [tendstoUniformlyOnFilter_iff_tendsto]; rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact fun i hi => (hf i hi).congr (hff'.mono fun x hx =>
    (Inseparable.rfl.prod hx).mem_open_iff hi.2)

/--
theorem `TendstoUniformlyOnFilter.congr` / 定理 `TendstoUniformlyOnFilter.congr`

English:
theorem TendstoUniformlyOnFilter.congr
  statement: {F' : ι -> α -> β} (hf : TendstoUniformlyOnFilter F f p p')
  proof: hf.congr_inseparable (hff'.mono fun _ h => .of_eq h)

中文:
定理 TendstoUniformlyOnFilter.congr
  结论: {F' : ι -> α -> β} (hf : TendstoUniformlyOnFilter F f p p')
  证明: hf.congr_inseparable (hff'.mono fun _ h => .of_eq h)

Depends on / 依赖: congr_inseparable, hf.congr_inseparable, of_eq
-/
theorem TendstoUniformlyOnFilter.congr {F' : ι -> α -> β} (hf : TendstoUniformlyOnFilter F f p p')
    (hff' : forallᶠ n : ι × α in p ×ˢ p', F n.fst n.snd = F' n.fst n.snd) :
    TendstoUniformlyOnFilter F' f p p' :=
  hf.congr_inseparable (hff'.mono fun _ h => .of_eq h)

/--
theorem `TendstoUniformlyOn.congr_inseparable` / 定理 `TendstoUniformlyOn.congr_inseparable`

English:
theorem TendstoUniformlyOn.congr_inseparable
  statement: {F' : ι -> α -> β} (hf : TendstoUniformlyOn F f p s)
  proof: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at hf ⊢
  refine hf.congr_inseparable ?_
  rwa [eventually_prod_principal_iff]

中文:
定理 TendstoUniformlyOn.congr_inseparable
  结论: {F' : ι -> α -> β} (hf : TendstoUniformlyOn F f p s)
  证明: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at hf ⊢
  refine hf.congr_inseparable ?_
  rwa [eventually_prod_principal_iff]

Depends on / 依赖: congr_inseparable, eventually_prod_principal_iff, hf.congr_inseparable, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter
-/
theorem TendstoUniformlyOn.congr_inseparable {F' : ι -> α -> β} (hf : TendstoUniformlyOn F f p s)
    (hff' : forallᶠ n in p, forall x in s, Inseparable (F n x) (F' n x)) : TendstoUniformlyOn F' f p s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at hf ⊢
  refine hf.congr_inseparable ?_
  rwa [eventually_prod_principal_iff]

/--
theorem `TendstoUniformlyOn.congr` / 定理 `TendstoUniformlyOn.congr`

English:
theorem TendstoUniformlyOn.congr
  statement: {F' : ι -> α -> β} (hf : TendstoUniformlyOn F f p s)
  proof: hf.congr_inseparable (hff'.mono fun _ h _ hx => .of_eq (h hx))

中文:
定理 TendstoUniformlyOn.congr
  结论: {F' : ι -> α -> β} (hf : TendstoUniformlyOn F f p s)
  证明: hf.congr_inseparable (hff'.mono fun _ h _ hx => .of_eq (h hx))

Depends on / 依赖: congr_inseparable, hf.congr_inseparable, of_eq
-/
theorem TendstoUniformlyOn.congr {F' : ι -> α -> β} (hf : TendstoUniformlyOn F f p s)
    (hff' : forallᶠ n in p, Set.EqOn (F n) (F' n) s) : TendstoUniformlyOn F' f p s :=
  hf.congr_inseparable (hff'.mono fun _ h _ hx => .of_eq (h hx))

/--
lemma `tendstoUniformly_congr_inseparable` / 引理 `tendstoUniformly_congr_inseparable`

English:
lemma tendstoUniformly_congr_inseparable
  statement: {F' : ι -> α -> β}
  proof: by
  rw [← tendstoUniformlyOn_univ]; rw [← tendstoUniformlyOn_univ]
  exact ⟨fun h => h.congr_inseparable (hF.mono fun _ hx y _ => hx y),
    fun h => h.congr_inseparable (hF.mono fun _ hx y _ => (hx y).symm)⟩

中文:
引理 tendstoUniformly_congr_inseparable
  结论: {F' : ι -> α -> β}
  证明: by
  rw [← tendstoUniformlyOn_univ]; rw [← tendstoUniformlyOn_univ]
  exact ⟨fun h => h.congr_inseparable (hF.mono fun _ hx y _ => hx y),
    fun h => h.congr_inseparable (hF.mono fun _ hx y _ => (hx y).symm)⟩

Depends on / 依赖: congr_inseparable, h.congr_inseparable, hF.mono, tendstoUniformlyOn_univ
-/
lemma tendstoUniformly_congr_inseparable {F' : ι -> α -> β}
    (hF : forallᶠ x in p, forall y, Inseparable (F x y) (F' x y)) :
    TendstoUniformly F f p ↔ TendstoUniformly F' f p := by
  rw [← tendstoUniformlyOn_univ]; rw [← tendstoUniformlyOn_univ]
  exact ⟨fun h => h.congr_inseparable (hF.mono fun _ hx y _ => hx y),
    fun h => h.congr_inseparable (hF.mono fun _ hx y _ => (hx y).symm)⟩

/--
lemma `tendstoUniformly_congr` / 引理 `tendstoUniformly_congr`

English:
lemma tendstoUniformly_congr
  given: {F' : ι -> α -> β} (hF : F =ᶠ[p] F')
  proof: tendstoUniformly_congr_inseparable (hF.mono fun _ hx y => .of_eq (congrFun hx y))

中文:
引理 tendstoUniformly_congr
  条件: {F' : ι -> α -> β} (hF : F =ᶠ[p] F')
  证明: tendstoUniformly_congr_inseparable (hF.mono fun _ hx y => .of_eq (congrFun hx y))

Depends on / 依赖: hF.mono, of_eq, tendstoUniformly_congr_inseparable
-/
lemma tendstoUniformly_congr {F' : ι -> α -> β} (hF : F =ᶠ[p] F') :
    TendstoUniformly F f p ↔ TendstoUniformly F' f p :=
  tendstoUniformly_congr_inseparable (hF.mono fun _ hx y => .of_eq (congrFun hx y))

/--
theorem `TendstoUniformlyOn.congr_inseparable_right` / 定理 `TendstoUniformlyOn.congr_inseparable_right`

English:
theorem TendstoUniformlyOn.congr_inseparable_right
  statement: {g : α -> β} (hf : TendstoUniformlyOn F f p s)
  proof: by
  rw [tendstoUniformlyOn_iff_tendsto]; rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  refine forall₂_imp (fun i hi hf => ?_) hf
  rw [eventually_prod_principal_iff] at hf ⊢
  exact hf.mono fun x hx y hy => (((hfg y hy).prod .rfl).mem_open_iff hi.2).mp (hx y hy)

中文:
定理 TendstoUniformlyOn.congr_inseparable_right
  结论: {g : α -> β} (hf : TendstoUniformlyOn F f p s)
  证明: by
  rw [tendstoUniformlyOn_iff_tendsto]; rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  refine forall₂_imp (fun i hi hf => ?_) hf
  rw [eventually_prod_principal_iff] at hf ⊢
  exact hf.mono fun x hx y hy => (((hfg y hy).prod .rfl).mem_open_iff hi.2).mp (hx y hy)

Depends on / 依赖: eventually_prod_principal_iff, hf.mono, mem_open_iff, tendstoUniformlyOn_iff_tendsto, tendsto_right_iff, uniformity_hasBasis_open, uniformity_hasBasis_open.tendsto_right_iff
-/
theorem TendstoUniformlyOn.congr_inseparable_right {g : α -> β} (hf : TendstoUniformlyOn F f p s)
    (hfg : forall x in s, Inseparable (f x) (g x)) : TendstoUniformlyOn F g p s := by
  rw [tendstoUniformlyOn_iff_tendsto]; rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  refine forall₂_imp (fun i hi hf => ?_) hf
  rw [eventually_prod_principal_iff] at hf ⊢
  exact hf.mono fun x hx y hy => (((hfg y hy).prod .rfl).mem_open_iff hi.2).mp (hx y hy)

/--
theorem `TendstoUniformlyOn.congr_right` / 定理 `TendstoUniformlyOn.congr_right`

English:
theorem TendstoUniformlyOn.congr_right
  statement: {g : α -> β} (hf : TendstoUniformlyOn F f p s)
  proof: hf.congr_inseparable_right fun _ hx => .of_eq (hfg hx)

中文:
定理 TendstoUniformlyOn.congr_right
  结论: {g : α -> β} (hf : TendstoUniformlyOn F f p s)
  证明: hf.congr_inseparable_right fun _ hx => .of_eq (hfg hx)

Depends on / 依赖: congr_inseparable_right, hf.congr_inseparable_right, of_eq
-/
theorem TendstoUniformlyOn.congr_right {g : α -> β} (hf : TendstoUniformlyOn F f p s)
    (hfg : EqOn f g s) : TendstoUniformlyOn F g p s :=
  hf.congr_inseparable_right fun _ hx => .of_eq (hfg hx)

/--
theorem `TendstoUniformly.tendstoUniformlyOn` / 定理 `TendstoUniformly.tendstoUniformlyOn`

English:
theorem TendstoUniformly.tendstoUniformlyOn
  given: (h : TendstoUniformly F f p)
  proof: (tendstoUniformlyOn_univ.2 h).mono (subset_univ s)

中文:
定理 TendstoUniformly.tendstoUniformlyOn
  条件: (h : TendstoUniformly F f p)
  证明: (tendstoUniformlyOn_univ.2 h).mono (subset_univ s)
-/
protected theorem TendstoUniformly.tendstoUniformlyOn (h : TendstoUniformly F f p) :
    TendstoUniformlyOn F f p s :=
  (tendstoUniformlyOn_univ.2 h).mono (subset_univ s)

/--
theorem `TendstoUniformlyOnFilter.comp` / 定理 `TendstoUniformlyOnFilter.comp`

English:
theorem TendstoUniformlyOnFilter.comp
  given: (h : TendstoUniformlyOnFilter F f p p') (g : γ -> α)
  proof: by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h ⊢
  exact h.comp (tendsto_id.prodMap tendsto_comap)

中文:
定理 TendstoUniformlyOnFilter.comp
  条件: (h : TendstoUniformlyOnFilter F f p p') (g : γ -> α)
  证明: by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h ⊢
  exact h.comp (tendsto_id.prodMap tendsto_comap)

Depends on / 依赖: h.comp, prodMap, tendstoUniformlyOnFilter_iff_tendsto, tendsto_comap, tendsto_id, tendsto_id.prodMap
-/
theorem TendstoUniformlyOnFilter.comp (h : TendstoUniformlyOnFilter F f p p') (g : γ -> α) :
    TendstoUniformlyOnFilter (fun n => F n ∘ g) (f ∘ g) p (p'.comap g) := by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h ⊢
  exact h.comp (tendsto_id.prodMap tendsto_comap)

/--
theorem `TendstoUniformlyOn.comp` / 定理 `TendstoUniformlyOn.comp`

English:
theorem TendstoUniformlyOn.comp
  given: (h : TendstoUniformlyOn F f p s) (g : γ -> α)
  proof: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [TendstoUniformlyOn, comap_principal] using TendstoUniformlyOnFilter.comp h g

中文:
定理 TendstoUniformlyOn.comp
  条件: (h : TendstoUniformlyOn F f p s) (g : γ -> α)
  证明: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [TendstoUniformlyOn, comap_principal] using TendstoUniformlyOnFilter.comp h g

Depends on / 依赖: TendstoUniformlyOn, TendstoUniformlyOnFilter, TendstoUniformlyOnFilter.comp, comap_principal, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter
-/
theorem TendstoUniformlyOn.comp (h : TendstoUniformlyOn F f p s) (g : γ -> α) :
    TendstoUniformlyOn (fun n => F n ∘ g) (f ∘ g) p (g ⁻¹' s) := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [TendstoUniformlyOn, comap_principal] using TendstoUniformlyOnFilter.comp h g

/--
theorem `TendstoUniformly.comp` / 定理 `TendstoUniformly.comp`

English:
theorem TendstoUniformly.comp
  given: (h : TendstoUniformly F f p) (g : γ -> α)
  proof: by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [principal_univ, comap_principal] using h.comp g

中文:
定理 TendstoUniformly.comp
  条件: (h : TendstoUniformly F f p) (g : γ -> α)
  证明: by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [principal_univ, comap_principal] using h.comp g

Depends on / 依赖: comap_principal, h.comp, principal_univ, tendstoUniformly_iff_tendstoUniformlyOnFilter
-/
theorem TendstoUniformly.comp (h : TendstoUniformly F f p) (g : γ -> α) :
    TendstoUniformly (fun n => F n ∘ g) (f ∘ g) p := by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [principal_univ, comap_principal] using h.comp g

/--
theorem `UniformContinuous.comp_tendstoUniformlyOnFilter` / 定理 `UniformContinuous.comp_tendstoUniformlyOnFilter`

English:
theorem UniformContinuous.comp_tendstoUniformlyOnFilter
  statement: [UniformSpace γ] {g : β -> γ}
  proof: fun _u hu => h _ (hg hu)

中文:
定理 一致连续.comp_tendstoUniformlyOnFilter
  结论: [一致空间 γ] {g : β -> γ}
  证明: fun _u hu => h _ (hg hu)
-/
theorem UniformContinuous.comp_tendstoUniformlyOnFilter [UniformSpace γ] {g : β -> γ}
    (hg : UniformContinuous g) (h : TendstoUniformlyOnFilter F f p p') :
    TendstoUniformlyOnFilter (fun i => g ∘ F i) (g ∘ f) p p' := fun _u hu => h _ (hg hu)

/--
theorem `UniformContinuous.comp_tendstoUniformlyOn` / 定理 `UniformContinuous.comp_tendstoUniformlyOn`

English:
theorem UniformContinuous.comp_tendstoUniformlyOn
  statement: [UniformSpace γ] {g : β -> γ}
  proof: fun _u hu => h _ (hg hu)

中文:
定理 一致连续.comp_tendstoUniformlyOn
  结论: [一致空间 γ] {g : β -> γ}
  证明: fun _u hu => h _ (hg hu)
-/
theorem UniformContinuous.comp_tendstoUniformlyOn [UniformSpace γ] {g : β -> γ}
    (hg : UniformContinuous g) (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i => g ∘ F i) (g ∘ f) p s := fun _u hu => h _ (hg hu)

/--
theorem `UniformContinuous.comp_tendstoUniformly` / 定理 `UniformContinuous.comp_tendstoUniformly`

English:
theorem UniformContinuous.comp_tendstoUniformly
  statement: [UniformSpace γ] {g : β -> γ}
  proof: fun _u hu => h _ (hg hu)

中文:
定理 一致连续.comp_tendstoUniformly
  结论: [一致空间 γ] {g : β -> γ}
  证明: fun _u hu => h _ (hg hu)
-/
theorem UniformContinuous.comp_tendstoUniformly [UniformSpace γ] {g : β -> γ}
    (hg : UniformContinuous g) (h : TendstoUniformly F f p) :
    TendstoUniformly (fun i => g ∘ F i) (g ∘ f) p := fun _u hu => h _ (hg hu)

/--
theorem `TendstoUniformlyOnFilter.prodMap` / 定理 `TendstoUniformlyOnFilter.prodMap`

English:
theorem TendstoUniformlyOnFilter.prodMap
  statement: {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'}
  proof: by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h h' ⊢
  rw [uniformity_prod_eq_comap_prod]; rw [tendsto_comap_iff]; rw [← map_swap4_prod]; rw [tendsto_map'_iff]
  simpa using! h.prodMap h'

中文:
定理 TendstoUniformlyOnFilter.prodMap
  结论: {ι' α' β' : 类型} [一致空间 β'] {F' : ι' -> α' -> β'}
  证明: by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h h' ⊢
  rw [uniformity_prod_eq_comap_prod]; rw [tendsto_comap_iff]; rw [← map_swap4_prod]; rw [tendsto_map'_iff]
  simpa using! h.prodMap h'

Depends on / 依赖: _iff, h.prodMap, map_swap4_prod, prodMap, tendstoUniformlyOnFilter_iff_tendsto, tendsto_comap_iff, tendsto_map, uniformity_prod_eq_comap_prod
-/
theorem TendstoUniformlyOnFilter.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'}
    {f' : α' -> β'} {q : Filter ι'} {q' : Filter α'} (h : TendstoUniformlyOnFilter F f p p')
    (h' : TendstoUniformlyOnFilter F' f' q q') :
    TendstoUniformlyOnFilter (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ q)
      (p' ×ˢ q') := by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h h' ⊢
  rw [uniformity_prod_eq_comap_prod]; rw [tendsto_comap_iff]; rw [← map_swap4_prod]; rw [tendsto_map'_iff]
  simpa using! h.prodMap h'

/--
theorem `TendstoUniformlyOn.prodMap` / 定理 `TendstoUniformlyOn.prodMap`

English:
theorem TendstoUniformlyOn.prodMap
  statement: {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'}
  proof: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h h' ⊢
  simpa only [prod_principal_principal] using h.prodMap h'

中文:
定理 TendstoUniformlyOn.prodMap
  结论: {ι' α' β' : 类型} [一致空间 β'] {F' : ι' -> α' -> β'}
  证明: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h h' ⊢
  simpa only [prod_principal_principal] using h.prodMap h'

Depends on / 依赖: h.prodMap, prodMap, prod_principal_principal, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter
-/
theorem TendstoUniformlyOn.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'}
    {f' : α' -> β'} {p' : Filter ι'} {s' : Set α'} (h : TendstoUniformlyOn F f p s)
    (h' : TendstoUniformlyOn F' f' p' s') :
    TendstoUniformlyOn (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ p')
      (s ×ˢ s') := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h h' ⊢
  simpa only [prod_principal_principal] using h.prodMap h'

/--
theorem `TendstoUniformly.prodMap` / 定理 `TendstoUniformly.prodMap`

English:
theorem TendstoUniformly.prodMap
  statement: {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'}
  proof: by
  rw [← tendstoUniformlyOn_univ]; rw [← univ_prod_univ] at *
  exact h.prodMap h'

中文:
定理 TendstoUniformly.prodMap
  结论: {ι' α' β' : 类型} [一致空间 β'] {F' : ι' -> α' -> β'}
  证明: by
  rw [← tendstoUniformlyOn_univ]; rw [← univ_prod_univ] at *
  exact h.prodMap h'

Depends on / 依赖: h.prodMap, prodMap, tendstoUniformlyOn_univ, univ_prod_univ
-/
theorem TendstoUniformly.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'}
    {f' : α' -> β'} {p' : Filter ι'} (h : TendstoUniformly F f p) (h' : TendstoUniformly F' f' p') :
    TendstoUniformly (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ p') := by
  rw [← tendstoUniformlyOn_univ]; rw [← univ_prod_univ] at *
  exact h.prodMap h'

/--
theorem `TendstoUniformlyOnFilter.prodMk` / 定理 `TendstoUniformlyOnFilter.prodMk`

English:
theorem TendstoUniformlyOnFilter.prodMk
  statement: {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α -> β'}
  proof: fun u hu => ((h.prodMap h') u hu).diag_of_prod_right

中文:
定理 TendstoUniformlyOnFilter.prodMk
  结论: {ι' β' : 类型} [一致空间 β'] {F' : ι' -> α -> β'}
  证明: fun u hu => ((h.prodMap h') u hu).diag_of_prod_right

Depends on / 依赖: diag_of_prod_right, h.prodMap, prodMap
-/
theorem TendstoUniformlyOnFilter.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α -> β'}
    {f' : α -> β'} {q : Filter ι'} (h : TendstoUniformlyOnFilter F f p p')
    (h' : TendstoUniformlyOnFilter F' f' q p') :
    TendstoUniformlyOnFilter (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a))
      (p ×ˢ q) p' :=
  fun u hu => ((h.prodMap h') u hu).diag_of_prod_right

/--
theorem `TendstoUniformlyOn.prodMk` / 定理 `TendstoUniformlyOn.prodMk`

English:
theorem TendstoUniformlyOn.prodMk
  statement: {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α -> β'}
  proof: (congr_arg _ s.inter_self).mp ((h.prodMap h').comp Function.diag)

中文:
定理 TendstoUniformlyOn.prodMk
  结论: {ι' β' : 类型} [一致空间 β'] {F' : ι' -> α -> β'}
  证明: (congr_arg _ s.inter_self).mp ((h.prodMap h').comp Function.diag)
-/
protected theorem TendstoUniformlyOn.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α -> β'}
    {f' : α -> β'} {p' : Filter ι'} (h : TendstoUniformlyOn F f p s)
    (h' : TendstoUniformlyOn F' f' p' s) :
    TendstoUniformlyOn (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p ×ˢ p')
      s :=
  (congr_arg _ s.inter_self).mp ((h.prodMap h').comp Function.diag)

/--
theorem `TendstoUniformly.prodMk` / 定理 `TendstoUniformly.prodMk`

English:
theorem TendstoUniformly.prodMk
  statement: {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α -> β'} {f' : α -> β'}
  proof: (h.prodMap h').comp Function.diag

中文:
定理 TendstoUniformly.prodMk
  结论: {ι' β' : 类型} [一致空间 β'] {F' : ι' -> α -> β'} {f' : α -> β'}
  证明: (h.prodMap h').comp Function.diag

Depends on / 依赖: Function, Function.diag, h.prodMap, prodMap
-/
theorem TendstoUniformly.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α -> β'} {f' : α -> β'}
    {p' : Filter ι'} (h : TendstoUniformly F f p) (h' : TendstoUniformly F' f' p') :
    TendstoUniformly (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p ×ˢ p') :=
  (h.prodMap h').comp Function.diag

/--
theorem `tendsto_prod_filter_iff` / 定理 `tendsto_prod_filter_iff`

English:
theorem tendsto_prod_filter_iff
  given: {c : β}
  proof: by
  simp_rw [nhds_eq_comap_uniformity, tendsto_comap_iff]
  rfl

中文:
定理 tendsto_prod_filter_iff
  条件: {c : β}
  证明: by
  simp_rw [nhds_eq_comap_uniformity, tendsto_comap_iff]
  rfl

Depends on / 依赖: nhds_eq_comap_uniformity, simp_rw, tendsto_comap_iff
-/
theorem tendsto_prod_filter_iff {c : β} :
    Tendsto ↿F (p ×ˢ p') (𝓝 c) ↔ TendstoUniformlyOnFilter F (fun _ => c) p p' := by
  simp_rw [nhds_eq_comap_uniformity, tendsto_comap_iff]
  rfl

/--
theorem `tendsto_prod_principal_iff` / 定理 `tendsto_prod_principal_iff`

English:
theorem tendsto_prod_principal_iff
  given: {c : β}
  proof: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

中文:
定理 tendsto_prod_principal_iff
  条件: {c : β}
  证明: by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

Depends on / 依赖: tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendsto_prod_filter_iff
-/
theorem tendsto_prod_principal_iff {c : β} :
    Tendsto ↿F (p ×ˢ 𝓟 s) (𝓝 c) ↔ TendstoUniformlyOn F (fun _ => c) p s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

/--
theorem `tendsto_prod_top_iff` / 定理 `tendsto_prod_top_iff`

English:
theorem tendsto_prod_top_iff
  given: {c : β}
  proof: by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

中文:
定理 tendsto_prod_top_iff
  条件: {c : β}
  证明: by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

Depends on / 依赖: tendstoUniformly_iff_tendstoUniformlyOnFilter, tendsto_prod_filter_iff
-/
theorem tendsto_prod_top_iff {c : β} :
    Tendsto ↿F (p ×ˢ ⊤) (𝓝 c) ↔ TendstoUniformly F (fun _ => c) p := by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

/--
theorem `tendstoUniformlyOn_empty` / 定理 `tendstoUniformlyOn_empty`

English:
theorem tendstoUniformlyOn_empty
  statement: TendstoUniformlyOn F f p ∅
  proof: fun u _ => by simp

中文:
定理 tendstoUniformlyOn_empty
  结论: TendstoUniformlyOn F f p ∅
  证明: fun u _ => by simp
-/
theorem tendstoUniformlyOn_empty : TendstoUniformlyOn F f p ∅ := fun u _ => by simp

/--
theorem `tendstoUniformlyOn_singleton_iff_tendsto` / 定理 `tendstoUniformlyOn_singleton_iff_tendsto`

English:
theorem tendstoUniformlyOn_singleton_iff_tendsto
  proof: by
  simp_rw [tendstoUniformlyOn_iff_tendsto, Uniform.tendsto_nhds_right, tendsto_def]
  exact forall₂_congr fun u _ => by simp [preimage]

中文:
定理 tendstoUniformlyOn_singleton_iff_tendsto
  证明: by
  simp_rw [tendstoUniformlyOn_iff_tendsto, Uniform.tendsto_nhds_right, tendsto_def]
  exact forall₂_congr fun u _ => by simp [preimage]

Depends on / 依赖: Uniform, Uniform.tendsto_nhds_right, preimage, simp_rw, tendstoUniformlyOn_iff_tendsto, tendsto_def, tendsto_nhds_right
-/
theorem tendstoUniformlyOn_singleton_iff_tendsto :
    TendstoUniformlyOn F f p {x} ↔ Tendsto (fun n : ι => F n x) p (𝓝 (f x)) := by
  simp_rw [tendstoUniformlyOn_iff_tendsto, Uniform.tendsto_nhds_right, tendsto_def]
  exact forall₂_congr fun u _ => by simp [preimage]

/--
theorem `Filter.Tendsto.tendstoUniformlyOnFilter_const` / 定理 `Filter.Tendsto.tendstoUniformlyOnFilter_const`

English:
theorem Filter.Tendsto.tendstoUniformlyOnFilter_const
  statement: {g : ι -> β} {b : β} (hg : Tendsto g p (𝓝 b))
  proof: by
  simpa only [nhds_eq_comap_uniformity, tendsto_comap_iff] using! hg.comp (tendsto_fst (g := p'))

中文:
定理 滤子.收敛.tendstoUniformlyOnFilter_const
  结论: {g : ι -> β} {b : β} (hg : 收敛 g p (𝓝 b))
  证明: by
  simpa only [nhds_eq_comap_uniformity, tendsto_comap_iff] using! hg.comp (tendsto_fst (g := p'))

Depends on / 依赖: hg.comp, nhds_eq_comap_uniformity, tendsto_comap_iff, tendsto_fst
-/
theorem Filter.Tendsto.tendstoUniformlyOnFilter_const {g : ι -> β} {b : β} (hg : Tendsto g p (𝓝 b))
    (p' : Filter α) :
    TendstoUniformlyOnFilter (fun n : ι => fun _ : α => g n) (fun _ : α => b) p p' := by
  simpa only [nhds_eq_comap_uniformity, tendsto_comap_iff] using! hg.comp (tendsto_fst (g := p'))

/--
theorem `Filter.Tendsto.tendstoUniformlyOn_const` / 定理 `Filter.Tendsto.tendstoUniformlyOn_const`

English:
theorem Filter.Tendsto.tendstoUniformlyOn_const
  statement: {g : ι -> β} {b : β} (hg : Tendsto g p (𝓝 b))
  proof: tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const (𝓟 s))

中文:
定理 滤子.收敛.tendstoUniformlyOn_const
  结论: {g : ι -> β} {b : β} (hg : 收敛 g p (𝓝 b))
  证明: tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const (𝓟 s))

Depends on / 依赖: hg.tendstoUniformlyOnFilter_const, tendstoUniformlyOnFilter_const, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
-/
theorem Filter.Tendsto.tendstoUniformlyOn_const {g : ι -> β} {b : β} (hg : Tendsto g p (𝓝 b))
    (s : Set α) : TendstoUniformlyOn (fun n : ι => fun _ : α => g n) (fun _ : α => b) p s :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const (𝓟 s))

/--
theorem `Filter.Tendsto.tendstoUniformly_const` / 定理 `Filter.Tendsto.tendstoUniformly_const`

English:
theorem Filter.Tendsto.tendstoUniformly_const
  given: {g : ι -> β} {b : β} (hg : Tendsto g p (𝓝 b))
  proof: tendstoUniformly_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const _)

中文:
定理 滤子.收敛.tendstoUniformly_const
  条件: {g : ι -> β} {b : β} (hg : 收敛 g p (𝓝 b))
  证明: tendstoUniformly_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const _)

Depends on / 依赖: hg.tendstoUniformlyOnFilter_const, tendstoUniformlyOnFilter_const, tendstoUniformly_iff_tendstoUniformlyOnFilter, tendstoUniformly_iff_tendstoUniformlyOnFilter.mpr
-/
theorem Filter.Tendsto.tendstoUniformly_const {g : ι -> β} {b : β} (hg : Tendsto g p (𝓝 b)) :
    TendstoUniformly (fun n : ι => fun _ : α => g n) (fun _ : α => b) p :=
  tendstoUniformly_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const _)

/--
theorem `UniformContinuousOn.tendstoUniformlyOn` / 定理 `UniformContinuousOn.tendstoUniformlyOn`

English:
theorem UniformContinuousOn.tendstoUniformlyOn
  statement: [UniformSpace α] [UniformSpace γ] {U : Set α}
  proof: by
  set φ := fun q : α × β => ((x, q.2), q)
  rw [tendstoUniformlyOn_iff_tendsto]
  change Tendsto (Prod.map ↿F ↿F ∘ φ) (𝓝[U] x ×ˢ 𝓟 V) (𝓤 γ)
  simp only [nhdsWithin, Filter.prod_eq_inf, comap_inf, inf_assoc, comap_principal, inf_principal]
  refine Tendsto.comp hF
    (Tendsto.inf ?_ <| tendsto_pr

中文:
定理 UniformContinuousOn.tendstoUniformlyOn
  结论: [一致空间 α] [一致空间 γ] {U : 集合 α}
  证明: by
  set φ := fun q : α × β => ((x, q.2), q)
  rw [tendstoUniformlyOn_iff_tendsto]
  change Tendsto (Prod.map ↿F ↿F ∘ φ) (𝓝[U] x ×ˢ 𝓟 V) (𝓤 γ)
  simp only [nhdsWithin, Filter.prod_eq_inf, comap_inf, inf_assoc, comap_principal, inf_principal]
  refine Tendsto.comp hF
    (Tendsto.inf ?_ <| tendsto_pr

Depends on / 依赖: Filter, Filter.prod_eq_inf, Prod.map, Tendsto, Tendsto.comp, Tendsto.inf, comap_comap, comap_inf, comap_principal, inf_assoc, inf_principal, nhdsWithin, nhds_eq_comap_uniformity, prodMk, prod_eq_inf, tendstoUniformlyOn_iff_tendsto, tendsto_comap, tendsto_comap.prodMk, tendsto_comap_iff, tendsto_diag_uniformity
-/
theorem UniformContinuousOn.tendstoUniformlyOn [UniformSpace α] [UniformSpace γ] {U : Set α}
    {V : Set β} {F : α -> β -> γ} (hF : UniformContinuousOn ↿F (U ×ˢ V)) (hU : x in U) :
    TendstoUniformlyOn F (F x) (𝓝[U] x) V := by
  set φ := fun q : α × β => ((x, q.2), q)
  rw [tendstoUniformlyOn_iff_tendsto]
  change Tendsto (Prod.map ↿F ↿F ∘ φ) (𝓝[U] x ×ˢ 𝓟 V) (𝓤 γ)
  simp only [nhdsWithin, Filter.prod_eq_inf, comap_inf, inf_assoc, comap_principal, inf_principal]
  refine Tendsto.comp hF
    (Tendsto.inf ?_ <| tendsto_principal_principal.2 fun x hx => ⟨⟨hU, hx.2⟩, hx⟩)
  simp only [uniformity_prod_eq_comap_prod, tendsto_comap_iff,
    nhds_eq_comap_uniformity, comap_comap]
  exact tendsto_comap.prodMk (tendsto_diag_uniformity _ _)

/--
theorem `UniformContinuousOn.tendstoUniformly` / 定理 `UniformContinuousOn.tendstoUniformly`

English:
theorem UniformContinuousOn.tendstoUniformly
  statement: [UniformSpace α] [UniformSpace γ] {U : Set α}
  proof: by
  simpa only [tendstoUniformlyOn_univ, nhdsWithin_eq_nhds.2 hU]
    using hF.tendstoUniformlyOn (mem_of_mem_nhds hU)

中文:
定理 UniformContinuousOn.tendstoUniformly
  结论: [一致空间 α] [一致空间 γ] {U : 集合 α}
  证明: by
  simpa only [tendstoUniformlyOn_univ, nhdsWithin_eq_nhds.2 hU]
    using hF.tendstoUniformlyOn (mem_of_mem_nhds hU)

Depends on / 依赖: hF.tendstoUniformlyOn, mem_of_mem_nhds, nhdsWithin_eq_nhds, tendstoUniformlyOn, tendstoUniformlyOn_univ
-/
theorem UniformContinuousOn.tendstoUniformly [UniformSpace α] [UniformSpace γ] {U : Set α}
    (hU : U in 𝓝 x) {F : α -> β -> γ} (hF : UniformContinuousOn ↿F (U ×ˢ (univ : Set β))) :
    TendstoUniformly F (F x) (𝓝 x) := by
  simpa only [tendstoUniformlyOn_univ, nhdsWithin_eq_nhds.2 hU]
    using hF.tendstoUniformlyOn (mem_of_mem_nhds hU)

/--
theorem `UniformContinuous₂.tendstoUniformly` / 定理 `UniformContinuous₂.tendstoUniformly`

English:
theorem UniformContinuous₂.tendstoUniformly
  statement: [UniformSpace α] [UniformSpace γ] {f : α -> β -> γ}
  proof: UniformContinuousOn.tendstoUniformly univ_mem by rwa [univ_prod_univ, uniformContinuousOn_univ]

中文:
定理 UniformContinuous₂.tendstoUniformly
  结论: [一致空间 α] [一致空间 γ] {f : α -> β -> γ}
  证明: UniformContinuousOn.tendstoUniformly univ_mem by rwa [univ_prod_univ, uniformContinuousOn_univ]

Depends on / 依赖: UniformContinuousOn, UniformContinuousOn.tendstoUniformly, tendstoUniformly, uniformContinuousOn_univ, univ_mem, univ_prod_univ
-/
theorem UniformContinuous₂.tendstoUniformly [UniformSpace α] [UniformSpace γ] {f : α -> β -> γ}
    (h : UniformContinuous₂ f) : TendstoUniformly f (f x) (𝓝 x) :=
UniformContinuousOn.tendstoUniformly univ_mem by rwa [univ_prod_univ, uniformContinuousOn_univ]

namespace Filter.HasBasis

variable {X ιX ια ιβ : Type*}

/--
lemma `tendstoUniformlyOnFilter_iff_of_uniformity` / 引理 `tendstoUniformlyOnFilter_iff_of_uniformity`

English:
lemma tendstoUniformlyOnFilter_iff_of_uniformity
  statement: {F : X -> α -> β} {f : α -> β}
  proof: by
  rw [tendstoUniformlyOnFilter_iff_tendsto]; rw [hβ.tendsto_right_iff]

中文:
引理 tendstoUniformlyOnFilter_iff_of_uniformity
  结论: {F : X -> α -> β} {f : α -> β}
  证明: by
  rw [tendstoUniformlyOnFilter_iff_tendsto]; rw [hβ.tendsto_right_iff]

Depends on / 依赖: tendstoUniformlyOnFilter_iff_tendsto, tendsto_right_iff
-/
lemma tendstoUniformlyOnFilter_iff_of_uniformity {F : X -> α -> β} {f : α -> β}
    {l : Filter X} {l' : Filter α} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOnFilter F f l l' ↔
      (forall i, pβ i -> forallᶠ n in l ×ˢ l', (f n.2, F n.1 n.2) in sβ i) := by
  rw [tendstoUniformlyOnFilter_iff_tendsto]; rw [hβ.tendsto_right_iff]

/--
lemma `tendstoUniformlyOnFilter_iff` / 引理 `tendstoUniformlyOnFilter_iff`

English:
lemma tendstoUniformlyOnFilter_iff
  statement: {F : X -> α -> β} {f : α -> β}
  proof: by
  simp [hβ.tendstoUniformlyOnFilter_iff_of_uniformity, (hl.prod hl').eventually_iff]

中文:
引理 tendstoUniformlyOnFilter_iff
  结论: {F : X -> α -> β} {f : α -> β}
  证明: by
  simp [hβ.tendstoUniformlyOnFilter_iff_of_uniformity, (hl.prod hl').eventually_iff]

Depends on / 依赖: eventually_iff, hl.prod, tendstoUniformlyOnFilter_iff_of_uniformity
-/
lemma tendstoUniformlyOnFilter_iff {F : X -> α -> β} {f : α -> β}
    {l : Filter X} {l' : Filter α} {pX : ιX -> Prop} {sX : ιX -> Set X}
    {pα : ια -> Prop} {sα : ια -> Set α} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β × β)}
    (hl : l.HasBasis pX sX) (hl' : l'.HasBasis pα sα)
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOnFilter F f l l' ↔
      (forall i, pβ i -> exists j k, (pX j ∧ pα k) ∧ forall x a, x in sX j -> a in sα k -> (f a, F x a) in sβ i) := by
  simp [hβ.tendstoUniformlyOnFilter_iff_of_uniformity, (hl.prod hl').eventually_iff]

/--
lemma `tendstoUniformlyOn_iff_of_uniformity` / 引理 `tendstoUniformlyOn_iff_of_uniformity`

English:
lemma tendstoUniformlyOn_iff_of_uniformity
  statement: {F : X -> α -> β} {f : α -> β}
  proof: by
  simp_rw [tendstoUniformlyOn_iff_tendsto, hβ.tendsto_right_iff, eventually_prod_principal_iff]

中文:
引理 tendstoUniformlyOn_iff_of_uniformity
  结论: {F : X -> α -> β} {f : α -> β}
  证明: by
  simp_rw [tendstoUniformlyOn_iff_tendsto, hβ.tendsto_right_iff, eventually_prod_principal_iff]

Depends on / 依赖: eventually_prod_principal_iff, simp_rw, tendstoUniformlyOn_iff_tendsto, tendsto_right_iff
-/
lemma tendstoUniformlyOn_iff_of_uniformity {F : X -> α -> β} {f : α -> β}
    {l : Filter X} {s : Set α} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOn F f l s ↔
      (forall i, pβ i -> forallᶠ n in l, forall x in s, (f x, F n x) in sβ i) := by
  simp_rw [tendstoUniformlyOn_iff_tendsto, hβ.tendsto_right_iff, eventually_prod_principal_iff]

/--
lemma `tendstoUniformlyOn_iff` / 引理 `tendstoUniformlyOn_iff`

English:
lemma tendstoUniformlyOn_iff
  statement: {F : X -> α -> β} {f : α -> β}
  proof: by
  simp [hβ.tendstoUniformlyOn_iff_of_uniformity, hl.eventually_iff]

中文:
引理 tendstoUniformlyOn_iff
  结论: {F : X -> α -> β} {f : α -> β}
  证明: by
  simp [hβ.tendstoUniformlyOn_iff_of_uniformity, hl.eventually_iff]

Depends on / 依赖: eventually_iff, hl.eventually_iff, tendstoUniformlyOn_iff_of_uniformity
-/
lemma tendstoUniformlyOn_iff {F : X -> α -> β} {f : α -> β}
    {l : Filter X} {s : Set α} {pX : ιX -> Prop} {sX : ιX -> Set X} {pβ : ιβ -> Prop}
    {sβ : ιβ -> Set (β × β)} (hl : l.HasBasis pX sX) (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOn F f l s ↔
      (forall i, pβ i -> exists j, pX j ∧ forall ⦃x⦄, x in sX j -> forall a in s, (f a, F x a) in sβ i) := by
  simp [hβ.tendstoUniformlyOn_iff_of_uniformity, hl.eventually_iff]

/--
lemma `tendstoUniformly_iff_of_uniformity` / 引理 `tendstoUniformly_iff_of_uniformity`

English:
lemma tendstoUniformly_iff_of_uniformity
  statement: {F : X -> α -> β} {f : α -> β}
  proof: by
  simp_rw [← tendstoUniformlyOn_univ, hβ.tendstoUniformlyOn_iff_of_uniformity, mem_univ,
    true_imp_iff]

中文:
引理 tendstoUniformly_iff_of_uniformity
  结论: {F : X -> α -> β} {f : α -> β}
  证明: by
  simp_rw [← tendstoUniformlyOn_univ, hβ.tendstoUniformlyOn_iff_of_uniformity, mem_univ,
    true_imp_iff]

Depends on / 依赖: mem_univ, simp_rw, tendstoUniformlyOn_iff_of_uniformity, tendstoUniformlyOn_univ, true_imp_iff
-/
lemma tendstoUniformly_iff_of_uniformity {F : X -> α -> β} {f : α -> β}
    {l : Filter X} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformly F f l ↔
      (forall i, pβ i -> forallᶠ n in l, forall x, (f x, F n x) in sβ i) := by
  simp_rw [← tendstoUniformlyOn_univ, hβ.tendstoUniformlyOn_iff_of_uniformity, mem_univ,
    true_imp_iff]

/--
lemma `tendstoUniformly_iff` / 引理 `tendstoUniformly_iff`

English:
lemma tendstoUniformly_iff
  statement: {F : X -> α -> β} {f : α -> β}
  proof: by
  simp only [hβ.tendstoUniformly_iff_of_uniformity, hl.eventually_iff]

中文:
引理 tendstoUniformly_iff
  结论: {F : X -> α -> β} {f : α -> β}
  证明: by
  simp only [hβ.tendstoUniformly_iff_of_uniformity, hl.eventually_iff]

Depends on / 依赖: eventually_iff, hl.eventually_iff, tendstoUniformly_iff_of_uniformity
-/
lemma tendstoUniformly_iff {F : X -> α -> β} {f : α -> β}
    {l : Filter X} {pX : ιX -> Prop} {sX : ιX -> Set X} (hl : l.HasBasis pX sX)
    {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β × β)} (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformly F f l ↔
      (forall i, pβ i -> exists j, pX j ∧ forall ⦃x⦄, x in sX j -> forall a, (f a, F x a) in sβ i) := by
  simp only [hβ.tendstoUniformly_iff_of_uniformity, hl.eventually_iff]

end Filter.HasBasis

/--
Definition of `UniformCauchySeqOnFilter` / `UniformCauchySeqOnFilter` 的定义

English:
definition UniformCauchySeqOnFilter
  signature: (F : ι -> α -> β) (p : Filter ι) (p' : Filter α)
  body: forall u in 𝓤 β, forallᶠ m : (ι × ι) × α in (p ×ˢ p) ×ˢ p', (F m.fst.fst m.snd, F m.fst.snd m.snd) in u

中文:
定义 UniformCauchySeqOnFilter
  签名: (F : ι -> α -> β) (p : 滤子 ι) (p' : 滤子 α)
  定义体: forall u in 𝓤 β, forallᶠ m : (ι × ι) × α in (p ×ˢ p) ×ˢ p', (F m.fst.fst m.snd, F m.fst.snd m.snd) in u

Depends on / 依赖: m.fst.fst, m.fst.snd, m.snd
-/
def UniformCauchySeqOnFilter (F : ι -> α -> β) (p : Filter ι) (p' : Filter α) : Prop :=
  forall u in 𝓤 β, forallᶠ m : (ι × ι) × α in (p ×ˢ p) ×ˢ p', (F m.fst.fst m.snd, F m.fst.snd m.snd) in u

/--
Definition of `UniformCauchySeqOn` / `UniformCauchySeqOn` 的定义

English:
definition UniformCauchySeqOn
  signature: (F : ι -> α -> β) (p : Filter ι) (s : Set α)
  body: forall u in 𝓤 β, forallᶠ m : ι × ι in p ×ˢ p, forall x : α, x in s -> (F m.fst x, F m.snd x) in u

中文:
定义 UniformCauchySeqOn
  签名: (F : ι -> α -> β) (p : 滤子 ι) (s : 集合 α)
  定义体: forall u in 𝓤 β, forallᶠ m : ι × ι in p ×ˢ p, forall x : α, x in s -> (F m.fst x, F m.snd x) in u

Depends on / 依赖: m.fst, m.snd
-/
def UniformCauchySeqOn (F : ι -> α -> β) (p : Filter ι) (s : Set α) : Prop :=
  forall u in 𝓤 β, forallᶠ m : ι × ι in p ×ˢ p, forall x : α, x in s -> (F m.fst x, F m.snd x) in u

/--
theorem `uniformCauchySeqOn_iff_uniformCauchySeqOnFilter` / 定理 `uniformCauchySeqOn_iff_uniformCauchySeqOnFilter`

English:
theorem uniformCauchySeqOn_iff_uniformCauchySeqOnFilter
  proof: by
  simp only [UniformCauchySeqOn, UniformCauchySeqOnFilter]
  refine forall₂_congr fun u hu => ?_
  rw [eventually_prod_principal_iff]

中文:
定理 uniformCauchySeqOn_iff_uniformCauchySeqOnFilter
  证明: by
  simp only [UniformCauchySeqOn, UniformCauchySeqOnFilter]
  refine forall₂_congr fun u hu => ?_
  rw [eventually_prod_principal_iff]

Depends on / 依赖: UniformCauchySeqOn, UniformCauchySeqOnFilter, eventually_prod_principal_iff
-/
theorem uniformCauchySeqOn_iff_uniformCauchySeqOnFilter :
    UniformCauchySeqOn F p s ↔ UniformCauchySeqOnFilter F p (𝓟 s) := by
  simp only [UniformCauchySeqOn, UniformCauchySeqOnFilter]
  refine forall₂_congr fun u hu => ?_
  rw [eventually_prod_principal_iff]

/--
theorem `UniformCauchySeqOn.uniformCauchySeqOnFilter` / 定理 `UniformCauchySeqOn.uniformCauchySeqOnFilter`

English:
theorem UniformCauchySeqOn.uniformCauchySeqOnFilter
  given: (hF : UniformCauchySeqOn F p s)
  proof: by rwa [← uniformCauchySeqOn_iff_uniformCauchySeqOnFilter]

中文:
定理 UniformCauchySeqOn.uniformCauchySeqOnFilter
  条件: (hF : UniformCauchySeqOn F p s)
  证明: by rwa [← uniformCauchySeqOn_iff_uniformCauchySeqOnFilter]

Depends on / 依赖: uniformCauchySeqOn_iff_uniformCauchySeqOnFilter
-/
theorem UniformCauchySeqOn.uniformCauchySeqOnFilter (hF : UniformCauchySeqOn F p s) :
    UniformCauchySeqOnFilter F p (𝓟 s) := by rwa [← uniformCauchySeqOn_iff_uniformCauchySeqOnFilter]

/--
theorem `TendstoUniformlyOnFilter.uniformCauchySeqOnFilter` / 定理 `TendstoUniformlyOnFilter.uniformCauchySeqOnFilter`

English:
theorem TendstoUniformlyOnFilter.uniformCauchySeqOnFilter
  given: (hF : TendstoUniformlyOnFilter F f p p')
  proof: by
  intro u hu
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩
  have := tendsto_swap4_prod.eventually ((hF t ht).prod_mk (hF t ht))
  apply this.diag_of_prod_right.mono
  simp only [and_imp, Prod.forall]
  intro n1 n2 x hl hr
exact htmem SetRel.prodMk_mem_comp (htsymm hl) hr

中文:
定理 TendstoUniformlyOnFilter.uniformCauchySeqOnFilter
  条件: (hF : TendstoUniformlyOnFilter F f p p')
  证明: by
  intro u hu
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩
  have := tendsto_swap4_prod.eventually ((hF t ht).prod_mk (hF t ht))
  apply this.diag_of_prod_right.mono
  simp only [and_imp, Prod.forall]
  intro n1 n2 x hl hr
exact htmem SetRel.prodMk_mem_comp (htsymm hl) hr

Depends on / 依赖: Prod.forall, SetRel, SetRel.prodMk_mem_comp, and_imp, comp_symm_of_uniformity, diag_of_prod_right, eventually, htsymm, prodMk_mem_comp, prod_mk, tendsto_swap4_prod, tendsto_swap4_prod.eventually, this.diag_of_prod_right.mono
-/
theorem TendstoUniformlyOnFilter.uniformCauchySeqOnFilter (hF : TendstoUniformlyOnFilter F f p p') :
    UniformCauchySeqOnFilter F p p' := by
  intro u hu
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩
  have := tendsto_swap4_prod.eventually ((hF t ht).prod_mk (hF t ht))
  apply this.diag_of_prod_right.mono
  simp only [and_imp, Prod.forall]
  intro n1 n2 x hl hr
exact htmem SetRel.prodMk_mem_comp (htsymm hl) hr

/--
theorem `TendstoUniformlyOn.uniformCauchySeqOn` / 定理 `TendstoUniformlyOn.uniformCauchySeqOn`

English:
theorem TendstoUniformlyOn.uniformCauchySeqOn
  given: (hF : TendstoUniformlyOn F f p s)
  proof: uniformCauchySeqOn_iff_uniformCauchySeqOnFilter.mpr
    hF.tendstoUniformlyOnFilter.uniformCauchySeqOnFilter

中文:
定理 TendstoUniformlyOn.uniformCauchySeqOn
  条件: (hF : TendstoUniformlyOn F f p s)
  证明: uniformCauchySeqOn_iff_uniformCauchySeqOnFilter.mpr
    hF.tendstoUniformlyOnFilter.uniformCauchySeqOnFilter

Depends on / 依赖: hF.tendstoUniformlyOnFilter.uniformCauchySeqOnFilter, tendstoUniformlyOnFilter, uniformCauchySeqOnFilter, uniformCauchySeqOn_iff_uniformCauchySeqOnFilter, uniformCauchySeqOn_iff_uniformCauchySeqOnFilter.mpr
-/
theorem TendstoUniformlyOn.uniformCauchySeqOn (hF : TendstoUniformlyOn F f p s) :
    UniformCauchySeqOn F p s :=
  uniformCauchySeqOn_iff_uniformCauchySeqOnFilter.mpr
    hF.tendstoUniformlyOnFilter.uniformCauchySeqOnFilter

/--
theorem `UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto` / 定理 `UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto`

English:
theorem UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto
  proof: by
  rcases p.eq_or_neBot with rfl | _
  · simp only [TendstoUniformlyOnFilter, bot_prod, eventually_bot, implies_true]
  -- Proof idea: |f_n(x) - f(x)| ≤ |f_n(x) - f_m(x)| + |f_m(x) - f(x)|. We choose `n`
  -- so that |f_n(x) - f_m(x)| is uniformly small across `s` whenever `m ≥ n`. Then for
  -- a

中文:
定理 UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto
  证明: by
  rcases p.eq_or_neBot with rfl | _
  · simp only [TendstoUniformlyOnFilter, bot_prod, eventually_bot, implies_true]
  -- Proof idea: |f_n(x) - f(x)| ≤ |f_n(x) - f_m(x)| + |f_m(x) - f(x)|. We choose `n`
  -- so that |f_n(x) - f_m(x)| is uniformly small across `s` whenever `m ≥ n`. Then for
  -- a

Depends on / 依赖: TendstoUniformlyOnFilter, bot_prod, eq_or_neBot, eventually_bot, implies_true, p.eq_or_neBot
-/
theorem UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto
    (hF : UniformCauchySeqOnFilter F p p')
    (hF' : forallᶠ x : α in p', Tendsto (fun n => F n x) p (𝓝 (f x))) :
    TendstoUniformlyOnFilter F f p p' := by
  rcases p.eq_or_neBot with rfl | _
  · simp only [TendstoUniformlyOnFilter, bot_prod, eventually_bot, implies_true]
  -- Proof idea: |f_n(x) - f(x)| ≤ |f_n(x) - f_m(x)| + |f_m(x) - f(x)|. We choose `n`
  -- so that |f_n(x) - f_m(x)| is uniformly small across `s` whenever `m ≥ n`. Then for
  -- a fixed `x`, we choose `m` sufficiently large such that |f_m(x) - f(x)| is small.
  intro u hu
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩
  -- We will choose n, x, and m simultaneously. n and x come from hF. m comes from hF'
  -- But we need to promote hF' to the full product filter to use it
  have hmc : forallᶠ x in (p ×ˢ p) ×ˢ p', Tendsto (fun n : ι => F n x.snd) p (𝓝 (f x.snd)) := by
    rw [eventually_prod_iff]
    exact ⟨fun _ => True, by simp, _, hF', by simp⟩
  -- To apply filter operations we'll need to do some order manipulation
  rw [Filter.eventually_swap_iff]
  have := tendsto_prodAssoc.eventually (tendsto_prod_swap.eventually ((hF t ht).and hmc))
  apply this.curry.mono
  simp only [Equiv.prodAssoc_apply, eventually_and, eventually_const, Prod.snd_swap, Prod.fst_swap,
    and_imp, Prod.forall]
  -- Complete the proof
  intro x n hx hm'
  refine Set.mem_of_mem_of_subset ?_ htmem
  rw [Uniform.tendsto_nhds_right] at hm'
  have := hx.and (hm' ht)
  obtain ⟨m, hm⟩ := this.exists
  exact ⟨F m x, ⟨hm.2, htsymm hm.1⟩⟩

/--
theorem `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` / 定理 `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto`

English:
theorem UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
  statement: (hF : UniformCauchySeqOn F p s)
  proof: tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (hF.uniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto hF')

中文:
定理 UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
  结论: (hF : UniformCauchySeqOn F p s)
  证明: tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (hF.uniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto hF')

Depends on / 依赖: hF.uniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto, tendstoUniformlyOnFilter_of_tendsto, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr, uniformCauchySeqOnFilter
-/
theorem UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto (hF : UniformCauchySeqOn F p s)
    (hF' : forall x : α, x in s -> Tendsto (fun n => F n x) p (𝓝 (f x))) : TendstoUniformlyOn F f p s :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (hF.uniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto hF')

/--
theorem `UniformCauchySeqOnFilter.mono_left` / 定理 `UniformCauchySeqOnFilter.mono_left`

English:
theorem UniformCauchySeqOnFilter.mono_left
  statement: {p'' : Filter ι} (hf : UniformCauchySeqOnFilter F p p')
  proof: fun u hu =>
  (hf u hu).filter_mono (p'.prod_mono_left (Filter.prod_mono hp hp))

中文:
定理 UniformCauchySeqOnFilter.mono_left
  结论: {p'' : 滤子 ι} (hf : UniformCauchySeqOnFilter F p p')
  证明: fun u hu =>
  (hf u hu).filter_mono (p'.prod_mono_left (Filter.prod_mono hp hp))
-/
theorem UniformCauchySeqOnFilter.mono_left {p'' : Filter ι} (hf : UniformCauchySeqOnFilter F p p')
    (hp : p'' <= p) : UniformCauchySeqOnFilter F p'' p' := fun u hu =>
  (hf u hu).filter_mono (p'.prod_mono_left (Filter.prod_mono hp hp))

/--
theorem `UniformCauchySeqOnFilter.mono_right` / 定理 `UniformCauchySeqOnFilter.mono_right`

English:
theorem UniformCauchySeqOnFilter.mono_right
  statement: {p'' : Filter α} (hf : UniformCauchySeqOnFilter F p p')
  proof: fun u hu =>
  have := (hf u hu).filter_mono ((p ×ˢ p).prod_mono_right hp)
  this.mono (by simp)

中文:
定理 UniformCauchySeqOnFilter.mono_right
  结论: {p'' : 滤子 α} (hf : UniformCauchySeqOnFilter F p p')
  证明: fun u hu =>
  have := (hf u hu).filter_mono ((p ×ˢ p).prod_mono_right hp)
  this.mono (by simp)
-/
theorem UniformCauchySeqOnFilter.mono_right {p'' : Filter α} (hf : UniformCauchySeqOnFilter F p p')
    (hp : p'' <= p') : UniformCauchySeqOnFilter F p p'' := fun u hu =>
  have := (hf u hu).filter_mono ((p ×ˢ p).prod_mono_right hp)
  this.mono (by simp)

/--
theorem `UniformCauchySeqOn.mono` / 定理 `UniformCauchySeqOn.mono`

English:
theorem UniformCauchySeqOn.mono
  given: (hf : UniformCauchySeqOn F p s) (hss' : s' subseteq s)
  proof: by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  exact hf.mono_right (le_principal_iff.mpr <| mem_principal.mpr hss')

中文:
定理 UniformCauchySeqOn.mono
  条件: (hf : UniformCauchySeqOn F p s) (hss' : s' subseteq s)
  证明: by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  exact hf.mono_right (le_principal_iff.mpr <| mem_principal.mpr hss')

Depends on / 依赖: hf.mono_right, le_principal_iff, le_principal_iff.mpr, mem_principal, mem_principal.mpr, mono_right, uniformCauchySeqOn_iff_uniformCauchySeqOnFilter
-/
theorem UniformCauchySeqOn.mono (hf : UniformCauchySeqOn F p s) (hss' : s' subseteq s) :
    UniformCauchySeqOn F p s' := by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  exact hf.mono_right (le_principal_iff.mpr <| mem_principal.mpr hss')

/--
theorem `UniformCauchySeqOnFilter.comp` / 定理 `UniformCauchySeqOnFilter.comp`

English:
theorem UniformCauchySeqOnFilter.comp
  statement: {γ : Type*} (hf : UniformCauchySeqOnFilter F p p')
  proof: fun u hu => by
  obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := eventually_prod_iff.mp (hf u hu)
  rw [eventually_prod_iff]
  refine ⟨pa, hpa, pb ∘ g, ?_, fun hx _ hy => hpapb hx hy⟩
  exact eventually_comap.mpr (hpb.mono fun x hx y hy => by simp only [hx, hy, Function.comp_apply])

中文:
定理 UniformCauchySeqOnFilter.comp
  结论: {γ : 类型} (hf : UniformCauchySeqOnFilter F p p')
  证明: fun u hu => by
  obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := eventually_prod_iff.mp (hf u hu)
  rw [eventually_prod_iff]
  refine ⟨pa, hpa, pb ∘ g, ?_, fun hx _ hy => hpapb hx hy⟩
  exact eventually_comap.mpr (hpb.mono fun x hx y hy => by simp only [hx, hy, Function.comp_apply])

Depends on / 依赖: Function, Function.comp_apply, comp_apply, eventually_comap, eventually_comap.mpr, eventually_prod_iff, eventually_prod_iff.mp, hpb.mono
-/
theorem UniformCauchySeqOnFilter.comp {γ : Type*} (hf : UniformCauchySeqOnFilter F p p')
    (g : γ -> α) : UniformCauchySeqOnFilter (fun n => F n ∘ g) p (p'.comap g) := fun u hu => by
  obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := eventually_prod_iff.mp (hf u hu)
  rw [eventually_prod_iff]
  refine ⟨pa, hpa, pb ∘ g, ?_, fun hx _ hy => hpapb hx hy⟩
  exact eventually_comap.mpr (hpb.mono fun x hx y hy => by simp only [hx, hy, Function.comp_apply])

/--
theorem `UniformCauchySeqOn.comp` / 定理 `UniformCauchySeqOn.comp`

English:
theorem UniformCauchySeqOn.comp
  given: {γ : Type*} (hf : UniformCauchySeqOn F p s) (g : γ -> α)
  proof: by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  simpa only [UniformCauchySeqOn, comap_principal] using hf.comp g

中文:
定理 UniformCauchySeqOn.comp
  条件: {γ : 类型} (hf : UniformCauchySeqOn F p s) (g : γ -> α)
  证明: by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  simpa only [UniformCauchySeqOn, comap_principal] using hf.comp g

Depends on / 依赖: UniformCauchySeqOn, comap_principal, hf.comp, uniformCauchySeqOn_iff_uniformCauchySeqOnFilter
-/
theorem UniformCauchySeqOn.comp {γ : Type*} (hf : UniformCauchySeqOn F p s) (g : γ -> α) :
    UniformCauchySeqOn (fun n => F n ∘ g) p (g ⁻¹' s) := by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  simpa only [UniformCauchySeqOn, comap_principal] using hf.comp g

/--
theorem `UniformContinuous.comp_uniformCauchySeqOn` / 定理 `UniformContinuous.comp_uniformCauchySeqOn`

English:
theorem UniformContinuous.comp_uniformCauchySeqOn
  statement: [UniformSpace γ] {g : β -> γ}
  proof: fun _u hu => hf _ (hg hu)

中文:
定理 一致连续.comp_uniformCauchySeqOn
  结论: [一致空间 γ] {g : β -> γ}
  证明: fun _u hu => hf _ (hg hu)
-/
theorem UniformContinuous.comp_uniformCauchySeqOn [UniformSpace γ] {g : β -> γ}
    (hg : UniformContinuous g) (hf : UniformCauchySeqOn F p s) :
    UniformCauchySeqOn (fun n => g ∘ F n) p s := fun _u hu => hf _ (hg hu)

/--
theorem `UniformCauchySeqOn.prodMap` / 定理 `UniformCauchySeqOn.prodMap`

English:
theorem UniformCauchySeqOn.prodMap
  statement: {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'}
  proof: by
  intro u hu
  rw [uniformity_prod_eq_prod]; rw [mem_map]; rw [mem_prod_iff] at hu
  obtain ⟨v, hv, w, hw, hvw⟩ := hu
  simp_rw [mem_prod, and_imp, Prod.forall, Prod.map_apply]
  rw [← Set.image_subset_iff] at hvw
  apply (tendsto_swap4_prod.eventually ((h v hv).prod_mk (h' w hw))).mono
  intro x

中文:
定理 UniformCauchySeqOn.prodMap
  结论: {ι' α' β' : 类型} [一致空间 β'] {F' : ι' -> α' -> β'}
  证明: by
  intro u hu
  rw [uniformity_prod_eq_prod]; rw [mem_map]; rw [mem_prod_iff] at hu
  obtain ⟨v, hv, w, hw, hvw⟩ := hu
  simp_rw [mem_prod, and_imp, Prod.forall, Prod.map_apply]
  rw [← Set.image_subset_iff] at hvw
  apply (tendsto_swap4_prod.eventually ((h v hv).prod_mk (h' w hw))).mono
  intro x

Depends on / 依赖: Prod.forall, Prod.map_apply, Set.image_subset_iff, and_imp, eventually, image_subset_iff, map_apply, mem_map, mem_prod, mem_prod_iff, mk_mem_prod, prod_mk, simp_rw, tendsto_swap4_prod, tendsto_swap4_prod.eventually, uniformity_prod_eq_prod
-/
theorem UniformCauchySeqOn.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'}
    {p' : Filter ι'} {s' : Set α'} (h : UniformCauchySeqOn F p s)
    (h' : UniformCauchySeqOn F' p' s') :
    UniformCauchySeqOn (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (p ×ˢ p') (s ×ˢ s') := by
  intro u hu
  rw [uniformity_prod_eq_prod]; rw [mem_map]; rw [mem_prod_iff] at hu
  obtain ⟨v, hv, w, hw, hvw⟩ := hu
  simp_rw [mem_prod, and_imp, Prod.forall, Prod.map_apply]
  rw [← Set.image_subset_iff] at hvw
  apply (tendsto_swap4_prod.eventually ((h v hv).prod_mk (h' w hw))).mono
  intro x hx a b ha hb
  exact hvw ⟨_, mk_mem_prod (hx.1 a ha) (hx.2 b hb), rfl⟩

/--
theorem `UniformCauchySeqOn.prod` / 定理 `UniformCauchySeqOn.prod`

English:
theorem UniformCauchySeqOn.prod
  statement: {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α -> β'}
  proof: (congr_arg _ s.inter_self).mp ((h.prodMap h').comp Function.diag)

中文:
定理 UniformCauchySeqOn.乘积
  结论: {ι' β' : 类型} [一致空间 β'] {F' : ι' -> α -> β'}
  证明: (congr_arg _ s.inter_self).mp ((h.prodMap h').comp Function.diag)

Depends on / 依赖: Function, Function.diag, congr_arg, h.prodMap, inter_self, prodMap, s.inter_self
-/
theorem UniformCauchySeqOn.prod {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α -> β'}
    {p' : Filter ι'} (h : UniformCauchySeqOn F p s) (h' : UniformCauchySeqOn F' p' s) :
    UniformCauchySeqOn (fun (i : ι × ι') a => (F i.fst a, F' i.snd a)) (p ×ˢ p') s :=
  (congr_arg _ s.inter_self).mp ((h.prodMap h').comp Function.diag)

/--
theorem `UniformCauchySeqOn.prod'` / 定理 `UniformCauchySeqOn.prod'`

English:
theorem UniformCauchySeqOn.prod'
  statement: {β' : Type*} [UniformSpace β'] {F' : ι -> α -> β'}
  proof: fun u hu =>
  have hh : Tendsto (fun x : ι => (x, x)) p (p ×ˢ p) := tendsto_diag
  (hh.prodMap hh).eventually ((h.prod h') u hu)

中文:
定理 UniformCauchySeqOn.乘积'
  结论: {β' : 类型} [一致空间 β'] {F' : ι -> α -> β'}
  证明: fun u hu =>
  have hh : Tendsto (fun x : ι => (x, x)) p (p ×ˢ p) := tendsto_diag
  (hh.prodMap hh).eventually ((h.prod h') u hu)
-/
theorem UniformCauchySeqOn.prod' {β' : Type*} [UniformSpace β'] {F' : ι -> α -> β'}
    (h : UniformCauchySeqOn F p s) (h' : UniformCauchySeqOn F' p s) :
    UniformCauchySeqOn (fun (i : ι) a => (F i a, F' i a)) p s := fun u hu =>
  have hh : Tendsto (fun x : ι => (x, x)) p (p ×ˢ p) := tendsto_diag
  (hh.prodMap hh).eventually ((h.prod h') u hu)

/--
theorem `UniformCauchySeqOn.cauchy_map` / 定理 `UniformCauchySeqOn.cauchy_map`

English:
theorem UniformCauchySeqOn.cauchy_map
  given: [hp : NeBot p] (hf : UniformCauchySeqOn F p s) (hx : x in s)
  proof: by
  simp only [cauchy_map_iff, hp, true_and]
  intro u hu
  rw [mem_map]
  filter_upwards [hf u hu] with p hp using hp x hx

中文:
定理 UniformCauchySeqOn.cauchy_map
  条件: [hp : NeBot p] (hf : UniformCauchySeqOn F p s) (hx : x in s)
  证明: by
  simp only [cauchy_map_iff, hp, true_and]
  intro u hu
  rw [mem_map]
  filter_upwards [hf u hu] with p hp using hp x hx

Depends on / 依赖: cauchy_map_iff, filter_upwards, mem_map, true_and
-/
theorem UniformCauchySeqOn.cauchy_map [hp : NeBot p] (hf : UniformCauchySeqOn F p s) (hx : x in s) :
    Cauchy (map (fun i => F i x) p) := by
  simp only [cauchy_map_iff, hp, true_and]
  intro u hu
  rw [mem_map]
  filter_upwards [hf u hu] with p hp using hp x hx

/--
theorem `UniformCauchySeqOn.cauchySeq` / 定理 `UniformCauchySeqOn.cauchySeq`

English:
theorem UniformCauchySeqOn.cauchySeq
  statement: [Nonempty ι] [SemilatticeSup ι]
  proof: hf.cauchy_map (hp := atTop_neBot) hx

中文:
定理 UniformCauchySeqOn.cauchySeq
  结论: [非空 ι] [SemilatticeSup ι]
  证明: hf.cauchy_map (hp := atTop_neBot) hx

Depends on / 依赖: atTop_neBot, cauchy_map, hf.cauchy_map
-/
theorem UniformCauchySeqOn.cauchySeq [Nonempty ι] [SemilatticeSup ι]
    (hf : UniformCauchySeqOn F atTop s) (hx : x in s) :
    CauchySeq fun i => F i x :=
  hf.cauchy_map (hp := atTop_neBot) hx

section SeqTendsto

/--
theorem `tendstoUniformlyOn_of_seq_tendstoUniformlyOn` / 定理 `tendstoUniformlyOn_of_seq_tendstoUniformlyOn`

English:
theorem tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  statement: {l : Filter ι} [l.IsCountablyGenerated]
  proof: by
  rw [tendstoUniformlyOn_iff_tendsto]; rw [tendsto_iff_seq_tendsto]
  intro u hu
  rw [tendsto_prod_iff'] at hu
  specialize h (fun n => (u n).fst) hu.1
  rw [tendstoUniformlyOn_iff_tendsto] at h
  exact h.comp (tendsto_id.prodMk hu.2)

中文:
定理 tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  结论: {l : 滤子 ι} [l.是余untablyGenerated]
  证明: by
  rw [tendstoUniformlyOn_iff_tendsto]; rw [tendsto_iff_seq_tendsto]
  intro u hu
  rw [tendsto_prod_iff'] at hu
  specialize h (fun n => (u n).fst) hu.1
  rw [tendstoUniformlyOn_iff_tendsto] at h
  exact h.comp (tendsto_id.prodMk hu.2)

Depends on / 依赖: h.comp, prodMk, specialize, tendstoUniformlyOn_iff_tendsto, tendsto_id, tendsto_id.prodMk, tendsto_iff_seq_tendsto, tendsto_prod_iff
-/
theorem tendstoUniformlyOn_of_seq_tendstoUniformlyOn {l : Filter ι} [l.IsCountablyGenerated]
    (h : forall u : Nat -> ι, Tendsto u atTop l -> TendstoUniformlyOn (fun n => F (u n)) f atTop s) :
    TendstoUniformlyOn F f l s := by
  rw [tendstoUniformlyOn_iff_tendsto]; rw [tendsto_iff_seq_tendsto]
  intro u hu
  rw [tendsto_prod_iff'] at hu
  specialize h (fun n => (u n).fst) hu.1
  rw [tendstoUniformlyOn_iff_tendsto] at h
  exact h.comp (tendsto_id.prodMk hu.2)

/--
theorem `TendstoUniformlyOn.seq_tendstoUniformlyOn` / 定理 `TendstoUniformlyOn.seq_tendstoUniformlyOn`

English:
theorem TendstoUniformlyOn.seq_tendstoUniformlyOn
  statement: {l : Filter ι} (h : TendstoUniformlyOn F f l s)
  proof: by
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  exact h.comp ((hu.comp tendsto_fst).prodMk tendsto_snd)

中文:
定理 TendstoUniformlyOn.seq_tendstoUniformlyOn
  结论: {l : 滤子 ι} (h : TendstoUniformlyOn F f l s)
  证明: by
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  exact h.comp ((hu.comp tendsto_fst).prodMk tendsto_snd)

Depends on / 依赖: h.comp, hu.comp, prodMk, tendstoUniformlyOn_iff_tendsto, tendsto_fst, tendsto_snd
-/
theorem TendstoUniformlyOn.seq_tendstoUniformlyOn {l : Filter ι} (h : TendstoUniformlyOn F f l s)
    (u : Nat -> ι) (hu : Tendsto u atTop l) : TendstoUniformlyOn (fun n => F (u n)) f atTop s := by
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  exact h.comp ((hu.comp tendsto_fst).prodMk tendsto_snd)

/--
theorem `tendstoUniformlyOn_iff_seq_tendstoUniformlyOn` / 定理 `tendstoUniformlyOn_iff_seq_tendstoUniformlyOn`

English:
theorem tendstoUniformlyOn_iff_seq_tendstoUniformlyOn
  given: {l : Filter ι} [l.IsCountablyGenerated]
  proof: ⟨TendstoUniformlyOn.seq_tendstoUniformlyOn, tendstoUniformlyOn_of_seq_tendstoUniformlyOn⟩

中文:
定理 tendstoUniformlyOn_iff_seq_tendstoUniformlyOn
  条件: {l : 滤子 ι} [l.是余untablyGenerated]
  证明: ⟨TendstoUniformlyOn.seq_tendstoUniformlyOn, tendstoUniformlyOn_of_seq_tendstoUniformlyOn⟩

Depends on / 依赖: TendstoUniformlyOn, TendstoUniformlyOn.seq_tendstoUniformlyOn, seq_tendstoUniformlyOn, tendstoUniformlyOn_of_seq_tendstoUniformlyOn
-/
theorem tendstoUniformlyOn_iff_seq_tendstoUniformlyOn {l : Filter ι} [l.IsCountablyGenerated] :
    TendstoUniformlyOn F f l s ↔
      forall u : Nat -> ι, Tendsto u atTop l -> TendstoUniformlyOn (fun n => F (u n)) f atTop s :=
  ⟨TendstoUniformlyOn.seq_tendstoUniformlyOn, tendstoUniformlyOn_of_seq_tendstoUniformlyOn⟩

/--
theorem `tendstoUniformly_iff_seq_tendstoUniformly` / 定理 `tendstoUniformly_iff_seq_tendstoUniformly`

English:
theorem tendstoUniformly_iff_seq_tendstoUniformly
  given: {l : Filter ι} [l.IsCountablyGenerated]
  proof: by
  simp_rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformlyOn_iff_seq_tendstoUniformlyOn

中文:
定理 tendstoUniformly_iff_seq_tendstoUniformly
  条件: {l : 滤子 ι} [l.是余untablyGenerated]
  证明: by
  simp_rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformlyOn_iff_seq_tendstoUniformlyOn

Depends on / 依赖: simp_rw, tendstoUniformlyOn_iff_seq_tendstoUniformlyOn, tendstoUniformlyOn_univ
-/
theorem tendstoUniformly_iff_seq_tendstoUniformly {l : Filter ι} [l.IsCountablyGenerated] :
    TendstoUniformly F f l ↔
      forall u : Nat -> ι, Tendsto u atTop l -> TendstoUniformly (fun n => F (u n)) f atTop := by
  simp_rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformlyOn_iff_seq_tendstoUniformlyOn

end SeqTendsto

section

variable [NeBot p] {L : ι -> β} {ℓ : β}

/--
theorem `TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto` / 定理 `TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto`

English:
theorem TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto
  proof: by
  rw [tendsto_nhds_left]
  intro s hs
  rw [mem_map]; rw [Set.preimage]; rw [← eventually_iff]
  obtain ⟨t, ht, hts⟩ := comp3_mem_uniformity hs
  have p1 : forallᶠ i in p, (L i, ℓ) in t := tendsto_nhds_left.mp h3 ht
  have p2 : forallᶠ i in p, forallᶠ x in p', (F i x, L i) in t := by
    filter_u

中文:
定理 TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto
  证明: by
  rw [tendsto_nhds_left]
  intro s hs
  rw [mem_map]; rw [Set.preimage]; rw [← eventually_iff]
  obtain ⟨t, ht, hts⟩ := comp3_mem_uniformity hs
  have p1 : forallᶠ i in p, (L i, ℓ) in t := tendsto_nhds_left.mp h3 ht
  have p2 : forallᶠ i in p, forallᶠ x in p', (F i x, L i) in t := by
    filter_u

Depends on / 依赖: Set.preimage, comp3_mem_uniformity, eventually_iff, filter_upwards, mem_map, p1.and, p2.and, preimage, tendsto_nhds_left, tendsto_nhds_left.mp
-/
theorem TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto
    (h1 : TendstoUniformlyOnFilter F f p p') (h2 : forallᶠ i in p, Tendsto (F i) p' (𝓝 (L i)))
    (h3 : Tendsto L p (𝓝 ℓ)) : Tendsto f p' (𝓝 ℓ) := by
  rw [tendsto_nhds_left]
  intro s hs
  rw [mem_map]; rw [Set.preimage]; rw [← eventually_iff]
  obtain ⟨t, ht, hts⟩ := comp3_mem_uniformity hs
  have p1 : forallᶠ i in p, (L i, ℓ) in t := tendsto_nhds_left.mp h3 ht
  have p2 : forallᶠ i in p, forallᶠ x in p', (F i x, L i) in t := by
    filter_upwards [h2] with i h2 using tendsto_nhds_left.mp h2 ht
  have p3 : forallᶠ i in p, forallᶠ x in p', (f x, F i x) in t := (h1 t ht).curry
  obtain ⟨i, p4, p5, p6⟩ := (p1.and (p2.and p3)).exists
  filter_upwards [p5, p6] with x p5 p6 using hts ⟨F i x, p6, L i, p5, p4⟩

/--
theorem `TendstoUniformly.tendsto_of_eventually_tendsto` / 定理 `TendstoUniformly.tendsto_of_eventually_tendsto`

English:
theorem TendstoUniformly.tendsto_of_eventually_tendsto
  proof: (h1.tendstoUniformlyOnFilter.mono_right le_top).tendsto_of_eventually_tendsto h2 h3

中文:
定理 TendstoUniformly.tendsto_of_eventually_tendsto
  证明: (h1.tendstoUniformlyOnFilter.mono_right le_top).tendsto_of_eventually_tendsto h2 h3

Depends on / 依赖: h1.tendstoUniformlyOnFilter.mono_right, le_top, mono_right, tendstoUniformlyOnFilter, tendsto_of_eventually_tendsto
-/
theorem TendstoUniformly.tendsto_of_eventually_tendsto
    (h1 : TendstoUniformly F f p) (h2 : forallᶠ i in p, Tendsto (F i) p' (𝓝 (L i)))
    (h3 : Tendsto L p (𝓝 ℓ)) : Tendsto f p' (𝓝 ℓ) :=
  (h1.tendstoUniformlyOnFilter.mono_right le_top).tendsto_of_eventually_tendsto h2 h3

end
