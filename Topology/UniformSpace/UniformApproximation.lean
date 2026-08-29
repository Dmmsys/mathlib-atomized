/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Uniform approximation

In this file, we give lemmas ensuring that a function is continuous if it can be approximated
uniformly by continuous functions. We give various versions, within a set or the whole space, at
a single point or at all points, with locally uniform approximation or uniform approximation. All
the statements are derived from a statement about locally uniform approximation within a set at
a point, called `continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt`.

## Implementation notes

Most results hold under weaker assumptions of locally uniform approximation. In a first section,
we prove the results under these weaker assumptions. Then, we derive the results on uniform
convergence from them.

## Tags

Uniform limit, uniform convergence, tends uniformly to
-/

public section


noncomputable section

open Topology Uniformity Filter SetRel Set Uniform

variable {α β ι : Type*} [TopologicalSpace α] [UniformSpace β]
variable {F : ι -> α -> β} {f : α -> β} {s s' : Set α} {x : α} {p : Filter ι} {g : ι -> α}

/--
theorem `continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt` / 定理 `continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt`

English:
theorem continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt
  statement: (hx : x in s)
  proof: by
  refine Uniform.continuousWithinAt_iff'_left.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : exists u in 𝓤 β, u ○ u subseteq u₀ := comp_mem_uniformity_sets hu₀
  obtain ⟨u₂, h₂, hsymm, u₂₁⟩ : exists u in 𝓤 β, (forall {a b}, (a, b) in u -> (b, a) in u) ∧ u ○ u subseteq u₁ :=
    comp_symm_of_uniformi

中文:
定理 continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt
  结论: (hx : x in s)
  证明: by
  refine Uniform.continuousWithinAt_iff'_left.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : exists u in 𝓤 β, u ○ u subseteq u₀ := comp_mem_uniformity_sets hu₀
  obtain ⟨u₂, h₂, hsymm, u₂₁⟩ : exists u in 𝓤 β, (forall {a b}, (a, b) in u -> (b, a) in u) ∧ u ○ u subseteq u₁ :=
    comp_symm_of_uniformi

Depends on / 依赖: Eventually, Eventually.mono, Uniform, Uniform.continuousWithinAt_iff, _left, comp_mem_uniformity_sets, comp_symm_of_uniformity, continuousWithinAt_iff, subseteq
-/
theorem continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (hx : x in s)
    (L : forall u in 𝓤 β, exists t in 𝓝[s] x, exists F : α -> β, ContinuousWithinAt F s x ∧ forall y in t, (f y, F y) in u) :
    ContinuousWithinAt f s x := by
  refine Uniform.continuousWithinAt_iff'_left.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : exists u in 𝓤 β, u ○ u subseteq u₀ := comp_mem_uniformity_sets hu₀
  obtain ⟨u₂, h₂, hsymm, u₂₁⟩ : exists u in 𝓤 β, (forall {a b}, (a, b) in u -> (b, a) in u) ∧ u ○ u subseteq u₁ :=
    comp_symm_of_uniformity h₁
  rcases L u₂ h₂ with ⟨t, tx, F, hFc, hF⟩
  have A : forallᶠ y in 𝓝[s] x, (f y, F y) in u₂ := Eventually.mono tx hF
  have B : forallᶠ y in 𝓝[s] x, (F y, F x) in u₂ := Uniform.continuousWithinAt_iff'_left.1 hFc h₂
  have C : forallᶠ y in 𝓝[s] x, (f y, F x) in u₁ :=
    (A.and B).mono fun y hy => u₂₁ (prodMk_mem_comp hy.1 hy.2)
  have : (F x, f x) in u₁ :=
    u₂₁ (prodMk_mem_comp (refl_mem_uniformity h₂) (hsymm (A.self_of_nhdsWithin hx)))
exact C.mono fun y hy => u₁₀ prodMk_mem_comp hy this

/--
theorem `continuousAt_of_locally_uniform_approx_of_continuousAt` / 定理 `continuousAt_of_locally_uniform_approx_of_continuousAt`

English:
theorem continuousAt_of_locally_uniform_approx_of_continuousAt
  proof: by
  rw [← continuousWithinAt_univ]
  apply continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (mem_univ _) _
  simpa only [exists_prop, nhdsWithin_univ, continuousWithinAt_univ] using L

中文:
定理 continuousAt_of_locally_uniform_approx_of_continuousAt
  证明: by
  rw [← continuousWithinAt_univ]
  apply continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (mem_univ _) _
  simpa only [exists_prop, nhdsWithin_univ, continuousWithinAt_univ] using L

Depends on / 依赖: continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt, continuousWithinAt_univ, exists_prop, mem_univ, nhdsWithin_univ
-/
theorem continuousAt_of_locally_uniform_approx_of_continuousAt
    (L : forall u in 𝓤 β, exists t in 𝓝 x, exists F, ContinuousAt F x ∧ forall y in t, (f y, F y) in u) :
    ContinuousAt f x := by
  rw [← continuousWithinAt_univ]
  apply continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (mem_univ _) _
  simpa only [exists_prop, nhdsWithin_univ, continuousWithinAt_univ] using L

/--
theorem `continuousOn_of_locally_uniform_approx_of_continuousWithinAt` / 定理 `continuousOn_of_locally_uniform_approx_of_continuousWithinAt`

English:
theorem continuousOn_of_locally_uniform_approx_of_continuousWithinAt
  proof: fun x hx =>
  continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt hx (L x hx)

中文:
定理 continuousOn_of_locally_uniform_approx_of_continuousWithinAt
  证明: fun x hx =>
  continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt hx (L x hx)
-/
theorem continuousOn_of_locally_uniform_approx_of_continuousWithinAt
    (L : forall x in s, forall u in 𝓤 β, exists t in 𝓝[s] x, exists F,
      ContinuousWithinAt F s x ∧ forall y in t, (f y, F y) in u) :
    ContinuousOn f s := fun x hx =>
  continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt hx (L x hx)

/--
theorem `continuousOn_of_uniform_approx_of_continuousOn` / 定理 `continuousOn_of_uniform_approx_of_continuousOn`

English:
theorem continuousOn_of_uniform_approx_of_continuousOn
  proof: continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun _x hx u hu =>
    ⟨s, self_mem_nhdsWithin, (L u hu).imp fun _F hF => ⟨hF.1.continuousWithinAt hx, hF.2⟩⟩

中文:
定理 continuousOn_of_uniform_approx_of_continuousOn
  证明: continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun _x hx u hu =>
    ⟨s, self_mem_nhdsWithin, (L u hu).imp fun _F hF => ⟨hF.1.continuousWithinAt hx, hF.2⟩⟩

Depends on / 依赖: continuousOn_of_locally_uniform_approx_of_continuousWithinAt, continuousWithinAt, self_mem_nhdsWithin
-/
theorem continuousOn_of_uniform_approx_of_continuousOn
    (L : forall u in 𝓤 β, exists F, ContinuousOn F s ∧ forall y in s, (f y, F y) in u) : ContinuousOn f s :=
  continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun _x hx u hu =>
    ⟨s, self_mem_nhdsWithin, (L u hu).imp fun _F hF => ⟨hF.1.continuousWithinAt hx, hF.2⟩⟩

/--
theorem `continuous_of_locally_uniform_approx_of_continuousAt` / 定理 `continuous_of_locally_uniform_approx_of_continuousAt`

English:
theorem continuous_of_locally_uniform_approx_of_continuousAt
  proof: continuous_iff_continuousAt.2 fun x =>
    continuousAt_of_locally_uniform_approx_of_continuousAt (L x)

中文:
定理 continuous_of_locally_uniform_approx_of_continuousAt
  证明: continuous_iff_continuousAt.2 fun x =>
    continuousAt_of_locally_uniform_approx_of_continuousAt (L x)

Depends on / 依赖: continuousAt_of_locally_uniform_approx_of_continuousAt, continuous_iff_continuousAt
-/
theorem continuous_of_locally_uniform_approx_of_continuousAt
    (L : forall x : α, forall u in 𝓤 β, exists t in 𝓝 x, exists F, ContinuousAt F x ∧ forall y in t, (f y, F y) in u) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x =>
    continuousAt_of_locally_uniform_approx_of_continuousAt (L x)

/--
theorem `continuous_of_uniform_approx_of_continuous` / 定理 `continuous_of_uniform_approx_of_continuous`

English:
theorem continuous_of_uniform_approx_of_continuous
  proof: continuousOn_univ.mp
continuousOn_of_uniform_approx_of_continuousOn by
      simpa [continuousOn_univ] using L

中文:
定理 continuous_of_uniform_approx_of_continuous
  证明: continuousOn_univ.mp
continuousOn_of_uniform_approx_of_continuousOn by
      simpa [continuousOn_univ] using L

Depends on / 依赖: continuousOn_of_uniform_approx_of_continuousOn, continuousOn_univ, continuousOn_univ.mp
-/
theorem continuous_of_uniform_approx_of_continuous
    (L : forall u in 𝓤 β, exists F, Continuous F ∧ forall y, (f y, F y) in u) : Continuous f :=
continuousOn_univ.mp
continuousOn_of_uniform_approx_of_continuousOn by
      simpa [continuousOn_univ] using L

/-!
### Uniform limits

From the previous statements on uniform approximation, we deduce continuity results for uniform
limits.
-/


/--
theorem `TendstoLocallyUniformlyOn.continuousOn` / 定理 `TendstoLocallyUniformlyOn.continuousOn`

English:
theorem TendstoLocallyUniformlyOn.continuousOn
  statement: (h : TendstoLocallyUniformlyOn F f p s)
  proof: by
  refine continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun x hx u hu => ?_
  rcases h u hu x hx with ⟨t, ht, H⟩
  rcases (hc.and_eventually H).exists with ⟨n, hFc, hF⟩
  exact ⟨t, ht, ⟨F n, hFc.continuousWithinAt hx, hF⟩⟩

中文:
定理 TendstoLocallyUniformlyOn.continuousOn
  结论: (h : TendstoLocallyUniformlyOn F f p s)
  证明: by
  refine continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun x hx u hu => ?_
  rcases h u hu x hx with ⟨t, ht, H⟩
  rcases (hc.and_eventually H).exists with ⟨n, hFc, hF⟩
  exact ⟨t, ht, ⟨F n, hFc.continuousWithinAt hx, hF⟩⟩
-/
protected theorem TendstoLocallyUniformlyOn.continuousOn (h : TendstoLocallyUniformlyOn F f p s)
    (hc : existsᶠ n in p, ContinuousOn (F n) s) : ContinuousOn f s := by
  refine continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun x hx u hu => ?_
  rcases h u hu x hx with ⟨t, ht, H⟩
  rcases (hc.and_eventually H).exists with ⟨n, hFc, hF⟩
  exact ⟨t, ht, ⟨F n, hFc.continuousWithinAt hx, hF⟩⟩

/--
theorem `TendstoUniformlyOn.continuousOn` / 定理 `TendstoUniformlyOn.continuousOn`

English:
theorem TendstoUniformlyOn.continuousOn
  statement: (h : TendstoUniformlyOn F f p s)
  proof: h.tendstoLocallyUniformlyOn.continuousOn hc

中文:
定理 TendstoUniformlyOn.continuousOn
  结论: (h : TendstoUniformlyOn F f p s)
  证明: h.tendstoLocallyUniformlyOn.continuousOn hc
-/
protected theorem TendstoUniformlyOn.continuousOn (h : TendstoUniformlyOn F f p s)
    (hc : existsᶠ n in p, ContinuousOn (F n) s) : ContinuousOn f s :=
  h.tendstoLocallyUniformlyOn.continuousOn hc

/--
theorem `TendstoLocallyUniformly.continuous` / 定理 `TendstoLocallyUniformly.continuous`

English:
theorem TendstoLocallyUniformly.continuous
  statement: (h : TendstoLocallyUniformly F f p)
  proof: continuousOn_univ.mp
h.tendstoLocallyUniformlyOn.continuousOn hc.mono fun _n hn => hn.continuousOn

中文:
定理 TendstoLocallyUniformly.continuous
  结论: (h : TendstoLocallyUniformly F f p)
  证明: continuousOn_univ.mp
h.tendstoLocallyUniformlyOn.continuousOn hc.mono fun _n hn => hn.continuousOn
-/
protected theorem TendstoLocallyUniformly.continuous (h : TendstoLocallyUniformly F f p)
    (hc : existsᶠ n in p, Continuous (F n)) : Continuous f :=
continuousOn_univ.mp
h.tendstoLocallyUniformlyOn.continuousOn hc.mono fun _n hn => hn.continuousOn

/--
theorem `TendstoUniformly.continuous` / 定理 `TendstoUniformly.continuous`

English:
theorem TendstoUniformly.continuous
  statement: (h : TendstoUniformly F f p)
  proof: h.tendstoLocallyUniformly.continuous hc

中文:
定理 TendstoUniformly.continuous
  结论: (h : TendstoUniformly F f p)
  证明: h.tendstoLocallyUniformly.continuous hc
-/
protected theorem TendstoUniformly.continuous (h : TendstoUniformly F f p)
    (hc : existsᶠ n in p, Continuous (F n)) : Continuous f :=
  h.tendstoLocallyUniformly.continuous hc

/-!
### Composing limits under uniform convergence

In general, if `Fₙ` converges pointwise to a function `f`, and `gₙ` tends to `x`, it is not true
that `Fₙ gₙ` tends to `f x`. It is true however if the convergence of `Fₙ` to `f` is uniform. In
this paragraph, we prove variations around this statement.
-/


/--
theorem `tendsto_comp_of_locally_uniform_limit_within` / 定理 `tendsto_comp_of_locally_uniform_limit_within`

English:
theorem tendsto_comp_of_locally_uniform_limit_within
  statement: (h : ContinuousWithinAt f s x)
  proof: by
  refine Uniform.tendsto_nhds_right.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : exists u in 𝓤 β, u ○ u subseteq u₀ := comp_mem_uniformity_sets hu₀
  rcases hunif u₁ h₁ with ⟨s, sx, hs⟩
  have A : forallᶠ n in p, g n in s := hg sx
  have B : forallᶠ n in p, (f x, f (g n)) in u₁ := hg (Uniform.cont

中文:
定理 tendsto_comp_of_locally_uniform_limit_within
  结论: (h : ContinuousWithinAt f s x)
  证明: by
  refine Uniform.tendsto_nhds_right.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : exists u in 𝓤 β, u ○ u subseteq u₀ := comp_mem_uniformity_sets hu₀
  rcases hunif u₁ h₁ with ⟨s, sx, hs⟩
  have A : forallᶠ n in p, g n in s := hg sx
  have B : forallᶠ n in p, (f x, f (g n)) in u₁ := hg (Uniform.cont

Depends on / 依赖: A.mp, B.mp, Uniform, Uniform.continuousWithinAt_iff, Uniform.tendsto_nhds_right, _right, comp_mem_uniformity_sets, continuousWithinAt_iff, hs.mono, prodMk_mem_comp, subseteq, tendsto_nhds_right
-/
theorem tendsto_comp_of_locally_uniform_limit_within (h : ContinuousWithinAt f s x)
    (hg : Tendsto g p (𝓝[s] x))
    (hunif : forall u in 𝓤 β, exists t in 𝓝[s] x, forallᶠ n in p, forall y in t, (f y, F n y) in u) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) := by
  refine Uniform.tendsto_nhds_right.2 fun u₀ hu₀ => ?_
  obtain ⟨u₁, h₁, u₁₀⟩ : exists u in 𝓤 β, u ○ u subseteq u₀ := comp_mem_uniformity_sets hu₀
  rcases hunif u₁ h₁ with ⟨s, sx, hs⟩
  have A : forallᶠ n in p, g n in s := hg sx
  have B : forallᶠ n in p, (f x, f (g n)) in u₁ := hg (Uniform.continuousWithinAt_iff'_right.1 h h₁)
exact B.mp A.mp hs.mono fun y H1 H2 H3 => u₁₀ prodMk_mem_comp H3 H1 _ H2

/--
theorem `tendsto_comp_of_locally_uniform_limit` / 定理 `tendsto_comp_of_locally_uniform_limit`

English:
theorem tendsto_comp_of_locally_uniform_limit
  statement: (h : ContinuousAt f x) (hg : Tendsto g p (𝓝 x))
  proof: by
  rw [← continuousWithinAt_univ] at h
  rw [← nhdsWithin_univ] at hunif hg
  exact tendsto_comp_of_locally_uniform_limit_within h hg hunif

中文:
定理 tendsto_comp_of_locally_uniform_limit
  结论: (h : ContinuousAt f x) (hg : 收敛 g p (𝓝 x))
  证明: by
  rw [← continuousWithinAt_univ] at h
  rw [← nhdsWithin_univ] at hunif hg
  exact tendsto_comp_of_locally_uniform_limit_within h hg hunif

Depends on / 依赖: continuousWithinAt_univ, nhdsWithin_univ, tendsto_comp_of_locally_uniform_limit_within
-/
theorem tendsto_comp_of_locally_uniform_limit (h : ContinuousAt f x) (hg : Tendsto g p (𝓝 x))
    (hunif : forall u in 𝓤 β, exists t in 𝓝 x, forallᶠ n in p, forall y in t, (f y, F n y) in u) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) := by
  rw [← continuousWithinAt_univ] at h
  rw [← nhdsWithin_univ] at hunif hg
  exact tendsto_comp_of_locally_uniform_limit_within h hg hunif

/--
theorem `TendstoLocallyUniformlyOn.tendsto_comp` / 定理 `TendstoLocallyUniformlyOn.tendsto_comp`

English:
theorem TendstoLocallyUniformlyOn.tendsto_comp
  statement: (h : TendstoLocallyUniformlyOn F f p s)
  proof: tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => h u hu x hx

中文:
定理 TendstoLocallyUniformlyOn.tendsto_comp
  结论: (h : TendstoLocallyUniformlyOn F f p s)
  证明: tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => h u hu x hx

Depends on / 依赖: tendsto_comp_of_locally_uniform_limit_within
-/
theorem TendstoLocallyUniformlyOn.tendsto_comp (h : TendstoLocallyUniformlyOn F f p s)
    (hf : ContinuousWithinAt f s x) (hx : x in s) (hg : Tendsto g p (𝓝[s] x)) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => h u hu x hx

/--
theorem `TendstoUniformlyOn.tendsto_comp` / 定理 `TendstoUniformlyOn.tendsto_comp`

English:
theorem TendstoUniformlyOn.tendsto_comp
  statement: (h : TendstoUniformlyOn F f p s)
  proof: tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => ⟨s, self_mem_nhdsWithin, h u hu⟩

中文:
定理 TendstoUniformlyOn.tendsto_comp
  结论: (h : TendstoUniformlyOn F f p s)
  证明: tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => ⟨s, self_mem_nhdsWithin, h u hu⟩

Depends on / 依赖: self_mem_nhdsWithin, tendsto_comp_of_locally_uniform_limit_within
-/
theorem TendstoUniformlyOn.tendsto_comp (h : TendstoUniformlyOn F f p s)
    (hf : ContinuousWithinAt f s x) (hg : Tendsto g p (𝓝[s] x)) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => ⟨s, self_mem_nhdsWithin, h u hu⟩

/--
theorem `TendstoLocallyUniformly.tendsto_comp` / 定理 `TendstoLocallyUniformly.tendsto_comp`

English:
theorem TendstoLocallyUniformly.tendsto_comp
  statement: (h : TendstoLocallyUniformly F f p)
  proof: tendsto_comp_of_locally_uniform_limit hf hg fun u hu => h u hu x

中文:
定理 TendstoLocallyUniformly.tendsto_comp
  结论: (h : TendstoLocallyUniformly F f p)
  证明: tendsto_comp_of_locally_uniform_limit hf hg fun u hu => h u hu x

Depends on / 依赖: tendsto_comp_of_locally_uniform_limit
-/
theorem TendstoLocallyUniformly.tendsto_comp (h : TendstoLocallyUniformly F f p)
    (hf : ContinuousAt f x) (hg : Tendsto g p (𝓝 x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit hf hg fun u hu => h u hu x

/--
theorem `TendstoUniformly.tendsto_comp` / 定理 `TendstoUniformly.tendsto_comp`

English:
theorem TendstoUniformly.tendsto_comp
  statement: (h : TendstoUniformly F f p) (hf : ContinuousAt f x)
  proof: h.tendstoLocallyUniformly.tendsto_comp hf hg

中文:
定理 TendstoUniformly.tendsto_comp
  结论: (h : TendstoUniformly F f p) (hf : ContinuousAt f x)
  证明: h.tendstoLocallyUniformly.tendsto_comp hf hg

Depends on / 依赖: h.tendstoLocallyUniformly.tendsto_comp, tendstoLocallyUniformly, tendsto_comp
-/
theorem TendstoUniformly.tendsto_comp (h : TendstoUniformly F f p) (hf : ContinuousAt f x)
    (hg : Tendsto g p (𝓝 x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  h.tendstoLocallyUniformly.tendsto_comp hf hg

/-!
### Uniform approximation and limit of uniformly continuous functions.
-/
section UniformContinuous
variable {α β ι : Type*} [UniformSpace α] [UniformSpace β]
variable {F : ι -> α -> β} {f : α -> β} {s : Set α} {p : Filter ι}

/--
theorem `uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn` / 定理 `uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn`

English:
theorem uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
  proof: by
  simp_rw [uniformContinuousOn_iff_restrict, uniformContinuous_def] at h ⊢
  intro u hu
  obtain ⟨v, hv, hvsymm, hvu⟩ := comp_comp_symm_mem_uniformity_sets hu
  obtain ⟨F, hF, hFv⟩ := h v hv
  filter_upwards [hF v hv] with x hx
exact hvu prodMk_mem_comp (prodMk_mem_comp (hFv _ x.1.prop) hx)
 hvsy

中文:
定理 uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
  证明: by
  simp_rw [uniformContinuousOn_iff_restrict, uniformContinuous_def] at h ⊢
  intro u hu
  obtain ⟨v, hv, hvsymm, hvu⟩ := comp_comp_symm_mem_uniformity_sets hu
  obtain ⟨F, hF, hFv⟩ := h v hv
  filter_upwards [hF v hv] with x hx
exact hvu prodMk_mem_comp (prodMk_mem_comp (hFv _ x.1.prop) hx)
 hvsy

Depends on / 依赖: comp_comp_symm_mem_uniformity_sets, filter_upwards, hvsymm, hvsymm.symm, prodMk_mem_comp, simp_rw, uniformContinuousOn_iff_restrict, uniformContinuous_def
-/
theorem uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
    (h : forall u in 𝓤 β, exists F : α -> β, UniformContinuousOn F s ∧ forall y in s, (f y, F y) in u) :
    UniformContinuousOn f s := by
  simp_rw [uniformContinuousOn_iff_restrict, uniformContinuous_def] at h ⊢
  intro u hu
  obtain ⟨v, hv, hvsymm, hvu⟩ := comp_comp_symm_mem_uniformity_sets hu
  obtain ⟨F, hF, hFv⟩ := h v hv
  filter_upwards [hF v hv] with x hx
exact hvu prodMk_mem_comp (prodMk_mem_comp (hFv _ x.1.prop) hx)
 hvsymm.symm (f x.2) (F x.2) hFv _ x.2.prop

/--
theorem `uniformContinuous_of_uniform_approx_of_uniformContinuous` / 定理 `uniformContinuous_of_uniform_approx_of_uniformContinuous`

English:
theorem uniformContinuous_of_uniform_approx_of_uniformContinuous
  proof: uniformContinuousOn_univ.mp uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
 by simpa [uniformContinuousOn_univ] using h

中文:
定理 uniformContinuous_of_uniform_approx_of_uniformContinuous
  证明: uniformContinuousOn_univ.mp uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
 by simpa [uniformContinuousOn_univ] using h

Depends on / 依赖: uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn, uniformContinuousOn_univ, uniformContinuousOn_univ.mp
-/
theorem uniformContinuous_of_uniform_approx_of_uniformContinuous
    (h : forall u in 𝓤 β, exists F : α -> β, UniformContinuous F ∧ forall y, (f y, F y) in u) :
    UniformContinuous f :=
uniformContinuousOn_univ.mp uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn
 by simpa [uniformContinuousOn_univ] using h

/--
theorem `TendstoUniformlyOn.uniformContinuousOn` / 定理 `TendstoUniformlyOn.uniformContinuousOn`

English:
theorem TendstoUniformlyOn.uniformContinuousOn
  statement: (h : TendstoUniformlyOn F f p s)
  proof: uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn fun u hu =>
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩

中文:
定理 TendstoUniformlyOn.uniformContinuousOn
  结论: (h : TendstoUniformlyOn F f p s)
  证明: uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn fun u hu =>
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩
-/
protected theorem TendstoUniformlyOn.uniformContinuousOn (h : TendstoUniformlyOn F f p s)
    (hc : existsᶠ n in p, UniformContinuousOn (F n) s) : UniformContinuousOn f s :=
  uniformContinuousOn_of_uniform_approx_of_uniformContinuousOn fun u hu =>
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩

/--
theorem `TendstoUniformly.uniformContinuous` / 定理 `TendstoUniformly.uniformContinuous`

English:
theorem TendstoUniformly.uniformContinuous
  statement: (h : TendstoUniformly F f p)
  proof: uniformContinuous_of_uniform_approx_of_uniformContinuous fun u hu =>
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩

中文:
定理 TendstoUniformly.uniformContinuous
  结论: (h : TendstoUniformly F f p)
  证明: uniformContinuous_of_uniform_approx_of_uniformContinuous fun u hu =>
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩
-/
protected theorem TendstoUniformly.uniformContinuous (h : TendstoUniformly F f p)
    (hc : existsᶠ n in p, UniformContinuous (F n)) : UniformContinuous f :=
  uniformContinuous_of_uniform_approx_of_uniformContinuous fun u hu =>
    let ⟨i, hF⟩ := (hc.and_eventually (h u hu)).exists
    ⟨F i, hF⟩

end UniformContinuous
