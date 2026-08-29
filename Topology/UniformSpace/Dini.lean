/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Dini's Theorem

This file proves Dini's theorem, which states that if `F n` is a monotone increasing sequence of
continuous real-valued functions on a compact set `s` converging pointwise to a continuous function
`f`, then `F n` converges uniformly to `f`.

We generalize the codomain from `ℝ` to a normed lattice additive commutative group `G`.
This theorem is true in a different generality as well: when `G` is a linearly ordered topological
group with the order topology. This weakens the norm assumption, in exchange for strengthening to
a linear order. This separate generality is not included in this file, but that generality was
included in initial drafts of the original
https://github.com/leanprover-community/mathlib4/pull/19068 and can be recovered if
necessary.

The key idea of the proof is to use a particular basis of `𝓝 0` which consists of open sets that
are somehow monotone in the sense that if `s` is in the basis, and `0 ≤ x ≤ y`, then
`y ∈ s → x ∈ s`, and so the proof would work on any topological ordered group possessing
such a basis. In the case of a linearly ordered topological group with the order topology, this
basis is `nhds_basis_Ioo`. In the case of a normed lattice additive commutative group, this basis
is `nhds_basis_ball`, and the fact that this basis satisfies the monotonicity criterion
corresponds to `HasSolidNorm`.
-/

public section

open Filter Topology

variable {ι α G : Type*} [Preorder ι] [TopologicalSpace α]
  [NormedAddCommGroup G] [Lattice G] [HasSolidNorm G] [IsOrderedAddMonoid G]

section Unbundled

open Metric

variable {F : ι -> α -> G} {f : α -> G}

namespace Monotone

/--
lemma `tendstoLocallyUniformly_of_forall_tendsto` / 引理 `tendstoLocallyUniformly_of_forall_tendsto`

English:
lemma tendstoLocallyUniformly_of_forall_tendsto
  proof: by
  refine (atTop : Filter ι).eq_or_neBot.elim (fun h => ?eq_bot) (fun _ => ?_)
  case eq_bot => simp [h, tendstoLocallyUniformly_iff_forall_tendsto]
  have F_le_f (x : α) (n : ι) : F n x <= f x := by
    refine _root_.ge_of_tendsto (h_tendsto x) ?_
    filter_upwards [Ici_mem_atTop n] with m hnm
 

中文:
引理 tendstoLocallyUniformly_of_对任意_tendsto
  证明: by
  refine (atTop : Filter ι).eq_or_neBot.elim (fun h => ?eq_bot) (fun _ => ?_)
  case eq_bot => simp [h, tendstoLocallyUniformly_iff_forall_tendsto]
  have F_le_f (x : α) (n : ι) : F n x <= f x := by
    refine _root_.ge_of_tendsto (h_tendsto x) ?_
    filter_upwards [Ici_mem_atTop n] with m hnm
 

Depends on / 依赖: F_le_f, Filter, Ici_mem_atTop, Metric, Metric.tendstoLocallyUniformly_iff, _root_, _root_.ge_of_tendsto, dist_eq_norm, eq_bot, eq_or_neBot, eq_or_neBot.elim, eventually, filter_upwards, ge_of_tendsto, hF_mono, h_tendsto, simp_rw, singlePass, tendstoLocallyUniformly_iff, tendstoLocallyUniformly_iff_forall_tendsto
-/
lemma tendstoLocallyUniformly_of_forall_tendsto
    (hF_cont : forall i, Continuous (F i)) (hF_mono : Monotone F) (hf : Continuous f)
    (h_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop := by
  refine (atTop : Filter ι).eq_or_neBot.elim (fun h => ?eq_bot) (fun _ => ?_)
  case eq_bot => simp [h, tendstoLocallyUniformly_iff_forall_tendsto]
  have F_le_f (x : α) (n : ι) : F n x <= f x := by
    refine _root_.ge_of_tendsto (h_tendsto x) ?_
    filter_upwards [Ici_mem_atTop n] with m hnm
    exact hF_mono hnm x
  simp_rw [Metric.tendstoLocallyUniformly_iff, dist_eq_norm']
  intro ε ε_pos x
  simp_rw +singlePass [tendsto_iff_norm_sub_tendsto_zero] at h_tendsto
.exists obtain ⟨n, hn⟩ := (h_tendsto x).eventually (eventually_lt_nhds ε_pos)
.mem_nhds hn, ?_⟩⟩ refine ⟨{y | ‖F n y - f y‖ < ε}, ⟨isOpen_lt (by fun_prop) continuous_const
  filter_upwards [eventually_ge_atTop n] with m hnm z hz
.trans_lt hz refine norm_le_norm_of_abs_le_abs ?_
  simp only [abs_of_nonpos (sub_nonpos_of_le (F_le_f _ _)), neg_sub, sub_le_sub_iff_left]
  exact hF_mono hnm z

/--
lemma `tendstoLocallyUniformlyOn_of_forall_tendsto` / 引理 `tendstoLocallyUniformlyOn_of_forall_tendsto`

English:
lemma tendstoLocallyUniformlyOn_of_forall_tendsto
  statement: {s : Set α}
  proof: by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  exact tendstoLocallyUniformly_of_forall_tendsto (hF_cont · |>.domRestrict)
    (fun _ _ h x => hF_mono _ x.2 h) hf.domRestrict (fun x => h_tendsto x x.2)

中文:
引理 tendstoLocallyUniformlyOn_of_对任意_tendsto
  结论: {s : 集合 α}
  证明: by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  exact tendstoLocallyUniformly_of_forall_tendsto (hF_cont · |>.domRestrict)
    (fun _ _ h x => hF_mono _ x.2 h) hf.domRestrict (fun x => h_tendsto x x.2)

Depends on / 依赖: domRestrict, hF_cont, hF_mono, h_tendsto, hf.domRestrict, tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, tendstoLocallyUniformly_of_forall_tendsto
-/
lemma tendstoLocallyUniformlyOn_of_forall_tendsto {s : Set α}
    (hF_cont : forall i, ContinuousOn (F i) s) (hF_mono : forall x in s, Monotone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f atTop s := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  exact tendstoLocallyUniformly_of_forall_tendsto (hF_cont · |>.domRestrict)
    (fun _ _ h x => hF_mono _ x.2 h) hf.domRestrict (fun x => h_tendsto x x.2)

/--
lemma `tendstoUniformly_of_forall_tendsto` / 引理 `tendstoUniformly_of_forall_tendsto`

English:
lemma tendstoUniformly_of_forall_tendsto
  statement: [CompactSpace α] (hF_cont : forall i, Continuous (F i))
  proof: tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp
    tendstoLocallyUniformly_of_forall_tendsto hF_cont hF_mono hf h_tendsto

中文:
引理 tendstoUniformly_of_对任意_tendsto
  结论: [紧空间 α] (hF_cont : 对任意 i, 连续 (F i))
  证明: tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp
    tendstoLocallyUniformly_of_forall_tendsto hF_cont hF_mono hf h_tendsto

Depends on / 依赖: hF_cont, hF_mono, h_tendsto, tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace, tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp, tendstoLocallyUniformly_of_forall_tendsto
-/
lemma tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : forall i, Continuous (F i))
    (hF_mono : Monotone F) (hf : Continuous f) (h_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace.mp
    tendstoLocallyUniformly_of_forall_tendsto hF_cont hF_mono hf h_tendsto

/--
lemma `tendstoUniformlyOn_of_forall_tendsto` / 引理 `tendstoUniformlyOn_of_forall_tendsto`

English:
lemma tendstoUniformlyOn_of_forall_tendsto
  statement: {s : Set α} (hs : IsCompact s)
  proof: .mp tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs
    tendstoLocallyUniformlyOn_of_forall_tendsto hF_cont hF_mono hf h_tendsto

中文:
引理 tendstoUniformlyOn_of_对任意_tendsto
  结论: {s : 集合 α} (hs : 是紧集 s)
  证明: .mp tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs
    tendstoLocallyUniformlyOn_of_forall_tendsto hF_cont hF_mono hf h_tendsto

Depends on / 依赖: hF_cont, hF_mono, h_tendsto, tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact, tendstoLocallyUniformlyOn_of_forall_tendsto
-/
lemma tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s)
    (hF_cont : forall i, ContinuousOn (F i) s) (hF_mono : forall x in s, Monotone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s :=
.mp tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs
    tendstoLocallyUniformlyOn_of_forall_tendsto hF_cont hF_mono hf h_tendsto

end Monotone

namespace Antitone

/--
lemma `tendstoLocallyUniformly_of_forall_tendsto` / 引理 `tendstoLocallyUniformly_of_forall_tendsto`

English:
lemma tendstoLocallyUniformly_of_forall_tendsto
  proof: Monotone.tendstoLocallyUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

中文:
引理 tendstoLocallyUniformly_of_对任意_tendsto
  证明: Monotone.tendstoLocallyUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

Depends on / 依赖: Monotone, Monotone.tendstoLocallyUniformly_of_forall_tendsto, hF_anti, hF_cont, h_tendsto, tendstoLocallyUniformly_of_forall_tendsto
-/
lemma tendstoLocallyUniformly_of_forall_tendsto
    (hF_cont : forall i, Continuous (F i)) (hF_anti : Antitone F) (hf : Continuous f)
    (h_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop :=
  Monotone.tendstoLocallyUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

/--
lemma `tendstoLocallyUniformlyOn_of_forall_tendsto` / 引理 `tendstoLocallyUniformlyOn_of_forall_tendsto`

English:
lemma tendstoLocallyUniformlyOn_of_forall_tendsto
  statement: {s : Set α}
  proof: Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

中文:
引理 tendstoLocallyUniformlyOn_of_对任意_tendsto
  结论: {s : 集合 α}
  证明: Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

Depends on / 依赖: Monotone, Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto, hF_anti, hF_cont, h_tendsto, tendstoLocallyUniformlyOn_of_forall_tendsto
-/
lemma tendstoLocallyUniformlyOn_of_forall_tendsto {s : Set α}
    (hF_cont : forall i, ContinuousOn (F i) s) (hF_anti : forall x in s, Antitone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformlyOn F f atTop s :=
  Monotone.tendstoLocallyUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

/--
lemma `tendstoUniformly_of_forall_tendsto` / 引理 `tendstoUniformly_of_forall_tendsto`

English:
lemma tendstoUniformly_of_forall_tendsto
  statement: [CompactSpace α] (hF_cont : forall i, Continuous (F i))
  proof: Monotone.tendstoUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

中文:
引理 tendstoUniformly_of_对任意_tendsto
  结论: [紧空间 α] (hF_cont : 对任意 i, 连续 (F i))
  证明: Monotone.tendstoUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

Depends on / 依赖: Monotone, Monotone.tendstoUniformly_of_forall_tendsto, hF_anti, hF_cont, h_tendsto, tendstoUniformly_of_forall_tendsto
-/
lemma tendstoUniformly_of_forall_tendsto [CompactSpace α] (hF_cont : forall i, Continuous (F i))
    (hF_anti : Antitone F) (hf : Continuous f) (h_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  Monotone.tendstoUniformly_of_forall_tendsto (G := Gᵒᵈ) hF_cont hF_anti hf h_tendsto

/--
lemma `tendstoUniformlyOn_of_forall_tendsto` / 引理 `tendstoUniformlyOn_of_forall_tendsto`

English:
lemma tendstoUniformlyOn_of_forall_tendsto
  statement: {s : Set α} (hs : IsCompact s)
  proof: Monotone.tendstoUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hs hF_cont hF_anti hf h_tendsto

中文:
引理 tendstoUniformlyOn_of_对任意_tendsto
  结论: {s : 集合 α} (hs : 是紧集 s)
  证明: Monotone.tendstoUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hs hF_cont hF_anti hf h_tendsto

Depends on / 依赖: Monotone, Monotone.tendstoUniformlyOn_of_forall_tendsto, hF_anti, hF_cont, h_tendsto, tendstoUniformlyOn_of_forall_tendsto
-/
lemma tendstoUniformlyOn_of_forall_tendsto {s : Set α} (hs : IsCompact s)
    (hF_cont : forall i, ContinuousOn (F i) s) (hF_anti : forall x in s, Antitone (F · x))
    (hf : ContinuousOn f s) (h_tendsto : forall x in s, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s :=
  Monotone.tendstoUniformlyOn_of_forall_tendsto (G := Gᵒᵈ) hs hF_cont hF_anti hf h_tendsto

end Antitone

end Unbundled

namespace ContinuousMap

variable {F : ι -> C(α, G)} {f : C(α, G)}

/--
lemma `tendsto_of_monotone_of_pointwise` / 引理 `tendsto_of_monotone_of_pointwise`

English:
lemma tendsto_of_monotone_of_pointwise
  statement: (hF_mono : Monotone F)
  proof: tendsto_of_tendstoLocallyUniformly
    hF_mono.tendstoLocallyUniformly_of_forall_tendsto (F · |>.continuous) f.continuous h_tendsto

中文:
引理 tendsto_of_monotone_of_pointwise
  结论: (hF_mono : 递增 F)
  证明: tendsto_of_tendstoLocallyUniformly
    hF_mono.tendstoLocallyUniformly_of_forall_tendsto (F · |>.continuous) f.continuous h_tendsto

Depends on / 依赖: continuous, f.continuous, hF_mono, hF_mono.tendstoLocallyUniformly_of_forall_tendsto, h_tendsto, tendstoLocallyUniformly_of_forall_tendsto, tendsto_of_tendstoLocallyUniformly
-/
lemma tendsto_of_monotone_of_pointwise (hF_mono : Monotone F)
    (h_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
tendsto_of_tendstoLocallyUniformly
    hF_mono.tendstoLocallyUniformly_of_forall_tendsto (F · |>.continuous) f.continuous h_tendsto

/--
lemma `tendsto_of_antitone_of_pointwise` / 引理 `tendsto_of_antitone_of_pointwise`

English:
lemma tendsto_of_antitone_of_pointwise
  statement: (hF_anti : Antitone F)
  proof: tendsto_of_monotone_of_pointwise (G := Gᵒᵈ) hF_anti h_tendsto

中文:
引理 tendsto_of_antitone_of_pointwise
  结论: (hF_anti : 递减 F)
  证明: tendsto_of_monotone_of_pointwise (G := Gᵒᵈ) hF_anti h_tendsto

Depends on / 依赖: hF_anti, h_tendsto, tendsto_of_monotone_of_pointwise
-/
lemma tendsto_of_antitone_of_pointwise (hF_anti : Antitone F)
    (h_tendsto : forall x, Tendsto (F · x) atTop (𝓝 (f x))) :
    Tendsto F atTop (𝓝 f) :=
  tendsto_of_monotone_of_pointwise (G := Gᵒᵈ) hF_anti h_tendsto

end ContinuousMap
