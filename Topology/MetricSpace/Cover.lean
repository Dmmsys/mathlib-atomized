/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Rel.Cover
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Covers in a metric space

This file defines covers, aka nets, which are a quantitative notion of compactness in a metric
space.

A `ε`-cover of a set `s` is a set `N` such that every element of `s` is at distance at most `ε` to
some element of `N`.

In a proper metric space, sets admitting a finite cover are precisely the relatively compact sets.

## References

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], Section 4.2.
-/

@[expose] public section

open Set
open scoped NNReal

namespace Metric
variable {X Y : Type*}

section PseudoEMetricSpace
variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {ε δ : Real>=0} {s t N N₁ N₂ : Set X} {x : X}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetRel.IsRefl {(x, y) : X × X | edist x y <= ε}
  body: by simp

中文:
实例 :
  签名: SetRel.IsRefl {(x, y) : X × X | edist x y <= ε}
  定义体: by simp
-/
instance : SetRel.IsRefl {(x, y) : X × X | edist x y <= ε} where refl := by simp
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetRel.IsSymm {(x, y) : X × X | edist x y <= ε}
  body: by simp [edist_comm]

中文:
实例 :
  签名: SetRel.是Symm {(x, y) : X × X | edist x y <= ε}
  定义体: by simp [edist_comm]

Depends on / 依赖: edist_comm
-/
instance : SetRel.IsSymm {(x, y) : X × X | edist x y <= ε} where symm := by simp [edist_comm]

/--
Definition of `IsCover` / `IsCover` 的定义

English:
definition IsCover
  signature: (ε : Real>=0) (s N : Set X)
  body: SetRel.IsCover {(x, y) | edist x y <= ε} s N

@[simp] protected nonrec lemma IsCover.empty : IsCover ε ∅ N := .empty

中文:
定义 IsCover
  签名: (ε : 实数>=0) (s N : 集合 X)
  定义体: SetRel.IsCover {(x, y) | edist x y <= ε} s N

@[simp] protected nonrec lemma IsCover.empty : IsCover ε ∅ N := .empty

Depends on / 依赖: IsCover, SetRel, SetRel.IsCover
-/
def IsCover (ε : Real>=0) (s N : Set X) : Prop := SetRel.IsCover {(x, y) | edist x y <= ε} s N

@[simp] protected nonrec lemma IsCover.empty : IsCover ε ∅ N := .empty

/--
lemma `isCover_empty_right` / 引理 `isCover_empty_right`

English:
lemma isCover_empty_right
  statement: IsCover ε s ∅ ↔ s = ∅
  proof: SetRel.isCover_empty_right

protected nonrec lemma IsCover.nonempty (hsN : IsCover ε s N) (hs : s.Nonempty) : N.Nonempty :=
  hsN.nonempty hs

中文:
引理 isCover_empty_right
  结论: IsCover ε s ∅ ↔ s = ∅
  证明: SetRel.isCover_empty_right

protected nonrec lemma IsCover.nonempty (hsN : IsCover ε s N) (hs : s.Nonempty) : N.Nonempty :=
  hsN.nonempty hs
-/
@[simp] lemma isCover_empty_right : IsCover ε s ∅ ↔ s = ∅ := SetRel.isCover_empty_right

protected nonrec lemma IsCover.nonempty (hsN : IsCover ε s N) (hs : s.Nonempty) : N.Nonempty :=
  hsN.nonempty hs

/--
lemma `IsCover.refl` / 引理 `IsCover.refl`

English:
lemma IsCover.refl
  given: (ε : Real>=0) (s : Set X)
  statement: IsCover ε s s
  proof: .rfl

中文:
引理 IsCover.refl
  条件: (ε : 实数>=0) (s : 集合 X)
  结论: IsCover ε s s
  证明: .rfl
-/
@[simp] lemma IsCover.refl (ε : Real>=0) (s : Set X) : IsCover ε s s := .rfl
/--
lemma `IsCover.rfl` / 引理 `IsCover.rfl`

English:
lemma IsCover.rfl
  given: {ε : Real>=0} {s : Set X}
  statement: IsCover ε s s
  proof: refl ε s

nonrec lemma IsCover.mono (hN : N₁ subseteq N₂) (h₁ : IsCover ε s N₁) : IsCover ε s N₂ := h₁.mono hN

nonrec lemma IsCover.anti (hst : s subseteq t) (ht : IsCover ε t N) : IsCover ε s N := ht.anti hst

中文:
引理 IsCover.rfl
  条件: {ε : 实数>=0} {s : 集合 X}
  结论: IsCover ε s s
  证明: refl ε s

nonrec lemma IsCover.mono (hN : N₁ subseteq N₂) (h₁ : IsCover ε s N₁) : IsCover ε s N₂ := h₁.mono hN

nonrec lemma IsCover.anti (hst : s subseteq t) (ht : IsCover ε t N) : IsCover ε s N := ht.anti hst
-/
lemma IsCover.rfl {ε : Real>=0} {s : Set X} : IsCover ε s s := refl ε s

nonrec lemma IsCover.mono (hN : N₁ subseteq N₂) (h₁ : IsCover ε s N₁) : IsCover ε s N₂ := h₁.mono hN

nonrec lemma IsCover.anti (hst : s subseteq t) (ht : IsCover ε t N) : IsCover ε s N := ht.anti hst

/--
lemma `IsCover.mono_radius` / 引理 `IsCover.mono_radius`

English:
lemma IsCover.mono_radius
  given: (hεδ : ε <= δ) (hε : IsCover ε s N)
  statement: IsCover δ s N
  proof: hε.mono_entourage fun xy hxy => by dsimp at *; exact le_trans hxy mod_cast hεδ

中文:
引理 IsCover.mono_radius
  条件: (hεδ : ε <= δ) (hε : IsCover ε s N)
  结论: IsCover δ s N
  证明: hε.mono_entourage fun xy hxy => by dsimp at *; exact le_trans hxy mod_cast hεδ

Depends on / 依赖: le_trans, mod_cast, mono_entourage
-/
lemma IsCover.mono_radius (hεδ : ε <= δ) (hε : IsCover ε s N) : IsCover δ s N :=
hε.mono_entourage fun xy hxy => by dsimp at *; exact le_trans hxy mod_cast hεδ

/--
lemma `IsCover.image_lipschitz` / 引理 `IsCover.image_lipschitz`

English:
lemma IsCover.image_lipschitz
  statement: {f : X -> Y} {s : Set X} {N : Set X} {ε K₂ : Real>=0}
  proof: by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x₀, hx₀, hcover⟩ := hs hx
  dsimp at *
  exact ⟨f x₀, ⟨x₀, hx₀, by grind⟩, by grw [hf x x₀, hcover]⟩

中文:
引理 IsCover.image_lipschitz
  结论: {f : X -> Y} {s : 集合 X} {N : 集合 X} {ε K₂ : 实数>=0}
  证明: by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x₀, hx₀, hcover⟩ := hs hx
  dsimp at *
  exact ⟨f x₀, ⟨x₀, hx₀, by grind⟩, by grw [hf x x₀, hcover]⟩

Depends on / 依赖: hcover
-/
lemma IsCover.image_lipschitz {f : X -> Y} {s : Set X} {N : Set X} {ε K₂ : Real>=0}
    (hs : IsCover ε s N) (hf : LipschitzWith K₂ f) : IsCover (K₂ * ε) (f '' s) (f '' N) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x₀, hx₀, hcover⟩ := hs hx
  dsimp at *
  exact ⟨f x₀, ⟨x₀, hx₀, by grind⟩, by grw [hf x x₀, hcover]⟩

/--
lemma `IsCover.image_lipschitz_of_surjective` / 引理 `IsCover.image_lipschitz_of_surjective`

English:
lemma IsCover.image_lipschitz_of_surjective
  statement: {f : X -> Y} {s : Set Y} {N : Set X} {ε K₂ : Real>=0}
  proof: by
  have : IsCover (K₂ * ε) (f '' s.preimage f) (f '' N) := IsCover.image_lipschitz hs hf
  simp_all only [image_preimage_eq]

中文:
引理 IsCover.image_lipschitz_of_surjective
  结论: {f : X -> Y} {s : 集合 Y} {N : 集合 X} {ε K₂ : 实数>=0}
  证明: by
  have : IsCover (K₂ * ε) (f '' s.preimage f) (f '' N) := IsCover.image_lipschitz hs hf
  simp_all only [image_preimage_eq]

Depends on / 依赖: IsCover, IsCover.image_lipschitz, image_lipschitz, image_preimage_eq, preimage, s.preimage
-/
lemma IsCover.image_lipschitz_of_surjective {f : X -> Y} {s : Set Y} {N : Set X} {ε K₂ : Real>=0}
    (hs : IsCover ε (s.preimage f) N) (hf : LipschitzWith K₂ f) (hf_surj : f.Surjective) :
    IsCover (K₂ * ε) s (f '' N) := by
  have : IsCover (K₂ * ε) (f '' s.preimage f) (f '' N) := IsCover.image_lipschitz hs hf
  simp_all only [image_preimage_eq]

/--
lemma `_root_.Isometry.isCover_image_iff` / 引理 `_root_.Isometry.isCover_image_iff`

English:
lemma _root_.Isometry.isCover_image_iff
  given: {f : X -> Y} (hf : Isometry f) (C : Set X)
  proof: by
  refine ⟨fun h x hx => ?_, fun h => by simpa using h.image_lipschitz hf.lipschitz⟩
  obtain ⟨c, hc_mem, hc⟩ := h (Set.mem_image_of_mem _ hx)
  obtain ⟨c', hc', rfl⟩ := hc_mem
  exact ⟨c', hc', le_of_eq_of_le (hf.edist_eq _ _).symm hc⟩

中文:
引理 _root_.等距.isCover_image_iff
  条件: {f : X -> Y} (hf : 等距 f) (C : 集合 X)
  证明: by
  refine ⟨fun h x hx => ?_, fun h => by simpa using h.image_lipschitz hf.lipschitz⟩
  obtain ⟨c, hc_mem, hc⟩ := h (Set.mem_image_of_mem _ hx)
  obtain ⟨c', hc', rfl⟩ := hc_mem
  exact ⟨c', hc', le_of_eq_of_le (hf.edist_eq _ _).symm hc⟩

Depends on / 依赖: Set.mem_image_of_mem, edist_eq, h.image_lipschitz, hc_mem, hf.edist_eq, hf.lipschitz, image_lipschitz, le_of_eq_of_le, lipschitz, mem_image_of_mem
-/
lemma _root_.Isometry.isCover_image_iff {f : X -> Y} (hf : Isometry f) (C : Set X) :
    IsCover ε (f '' s) (f '' C) ↔ IsCover ε s C := by
  refine ⟨fun h x hx => ?_, fun h => by simpa using h.image_lipschitz hf.lipschitz⟩
  obtain ⟨c, hc_mem, hc⟩ := h (Set.mem_image_of_mem _ hx)
  obtain ⟨c', hc', rfl⟩ := hc_mem
  exact ⟨c', hc', le_of_eq_of_le (hf.edist_eq _ _).symm hc⟩

/--
lemma `IsCover.singleton_of_ediam_le` / 引理 `IsCover.singleton_of_ediam_le`

English:
lemma IsCover.singleton_of_ediam_le
  given: (hA : ediam s <= ε) (hx : x in s)
  proof: fun _ h_mem => ⟨x, by simp, (edist_le_ediam_of_mem h_mem hx).trans hA⟩

中文:
引理 IsCover.singleton_of_ediam_le
  条件: (hA : ediam s <= ε) (hx : x in s)
  证明: fun _ h_mem => ⟨x, by simp, (edist_le_ediam_of_mem h_mem hx).trans hA⟩

Depends on / 依赖: edist_le_ediam_of_mem, h_mem
-/
lemma IsCover.singleton_of_ediam_le (hA : ediam s <= ε) (hx : x in s) :
    IsCover ε s ({x} : Set X) :=
  fun _ h_mem => ⟨x, by simp, (edist_le_ediam_of_mem h_mem hx).trans hA⟩

/--
lemma `isCover_iff_subset_iUnion_closedEBall` / 引理 `isCover_iff_subset_iUnion_closedEBall`

English:
lemma isCover_iff_subset_iUnion_closedEBall
  proof: by
  simp [IsCover, SetRel.IsCover, subset_def]

alias isCover_iff_subset_iUnion_emetricClosedBall :=
  isCover_iff_subset_iUnion_closedEBall

中文:
引理 isCover_iff_subset_iUnion_closedEBall
  证明: by
  simp [IsCover, SetRel.IsCover, subset_def]

alias isCover_iff_subset_iUnion_emetricClosedBall :=
  isCover_iff_subset_iUnion_closedEBall

Depends on / 依赖: IsCover, SetRel, SetRel.IsCover, subset_def
-/
lemma isCover_iff_subset_iUnion_closedEBall :
    IsCover ε s N ↔ s subseteq ⋃ y in N, Metric.closedEBall y ε := by
  simp [IsCover, SetRel.IsCover, subset_def]

alias isCover_iff_subset_iUnion_emetricClosedBall :=
  isCover_iff_subset_iUnion_closedEBall

/-- A maximal `ε`-separated subset of a set `s` is an `ε`-cover of `s`.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.6. -/
nonrec lemma IsCover.of_maximal_isSeparated (hN : Maximal (fun N => N subseteq s ∧ IsSeparated ε N) N) :
    IsCover ε s N :=
.of_maximal_isSeparated by simpa [isSeparated_iff_setRelIsSeparated] using hN

/--
lemma `exists_finite_isCover_of_totallyBounded` / 引理 `exists_finite_isCover_of_totallyBounded`

English:
lemma exists_finite_isCover_of_totallyBounded
  given: (hε : ε != 0) (hs : TotallyBounded s)
  proof: by
  rw [EMetric.totallyBounded_iff'] at hs
  obtain ⟨N, hNA, hN_finite, hN⟩ := hs ε (by positivity)
  simp only [isCover_iff_subset_iUnion_closedEBall]
  refine ⟨N, by simpa, by simpa, ?_⟩
  · refine hN.trans fun x hx => ?_
    simp only [Set.mem_iUnion, Metric.mem_eball, exists_prop, Metric.mem_cl

中文:
引理 存在_finite_isCover_of_totallyBounded
  条件: (hε : ε != 0) (hs : 全有界 s)
  证明: by
  rw [EMetric.totallyBounded_iff'] at hs
  obtain ⟨N, hNA, hN_finite, hN⟩ := hs ε (by positivity)
  simp only [isCover_iff_subset_iUnion_closedEBall]
  refine ⟨N, by simpa, by simpa, ?_⟩
  · refine hN.trans fun x hx => ?_
    simp only [Set.mem_iUnion, Metric.mem_eball, exists_prop, Metric.mem_cl

Depends on / 依赖: EMetric, EMetric.totallyBounded_iff, Metric, Metric.mem_closedEBall, Metric.mem_eball, Set.mem_iUnion, exists_prop, hN.trans, hN_finite, hy.le, isCover_iff_subset_iUnion_closedEBall, mem_closedEBall, mem_eball, mem_iUnion, totallyBounded_iff
-/
lemma exists_finite_isCover_of_totallyBounded (hε : ε != 0) (hs : TotallyBounded s) :
    exists N subseteq s, N.Finite ∧ IsCover ε s N := by
  rw [EMetric.totallyBounded_iff'] at hs
  obtain ⟨N, hNA, hN_finite, hN⟩ := hs ε (by positivity)
  simp only [isCover_iff_subset_iUnion_closedEBall]
  refine ⟨N, by simpa, by simpa, ?_⟩
  · refine hN.trans fun x hx => ?_
    simp only [Set.mem_iUnion, Metric.mem_eball, exists_prop, Metric.mem_closedEBall] at hx ⊢
    obtain ⟨y, hyN, hy⟩ := hx
    exact ⟨y, hyN, hy.le⟩

/--
lemma `exists_finite_isCover_of_isCompact_closure` / 引理 `exists_finite_isCover_of_isCompact_closure`

English:
lemma exists_finite_isCover_of_isCompact_closure
  given: (hε : ε != 0) (hs : IsCompact (closure s))
  proof: exists_finite_isCover_of_totallyBounded hε (hs.totallyBounded.subset subset_closure)

中文:
引理 存在_finite_isCover_of_isCompact_closure
  条件: (hε : ε != 0) (hs : 是紧集 (closure s))
  证明: exists_finite_isCover_of_totallyBounded hε (hs.totallyBounded.subset subset_closure)

Depends on / 依赖: exists_finite_isCover_of_totallyBounded, hs.totallyBounded.subset, subset, subset_closure, totallyBounded
-/
lemma exists_finite_isCover_of_isCompact_closure (hε : ε != 0) (hs : IsCompact (closure s)) :
    exists N subseteq s, N.Finite ∧ IsCover ε s N :=
  exists_finite_isCover_of_totallyBounded hε (hs.totallyBounded.subset subset_closure)

/--
lemma `exists_finite_isCover_of_isCompact` / 引理 `exists_finite_isCover_of_isCompact`

English:
lemma exists_finite_isCover_of_isCompact
  given: (hε : ε != 0) (hs : IsCompact s)
  proof: exists_finite_isCover_of_totallyBounded hε hs.totallyBounded

中文:
引理 存在_finite_isCover_of_isCompact
  条件: (hε : ε != 0) (hs : 是紧集 s)
  证明: exists_finite_isCover_of_totallyBounded hε hs.totallyBounded

Depends on / 依赖: exists_finite_isCover_of_totallyBounded, hs.totallyBounded, totallyBounded
-/
lemma exists_finite_isCover_of_isCompact (hε : ε != 0) (hs : IsCompact s) :
    exists N subseteq s, N.Finite ∧ IsCover ε s N :=
  exists_finite_isCover_of_totallyBounded hε hs.totallyBounded

end PseudoEMetricSpace

section PseudoMetricSpace
variable [PseudoMetricSpace X] {ε : Real>=0} {s N : Set X}

/--
lemma `isCover_iff_subset_iUnion_closedBall` / 引理 `isCover_iff_subset_iUnion_closedBall`

English:
lemma isCover_iff_subset_iUnion_closedBall
  statement: IsCover ε s N ↔ s subseteq ⋃ y in N, closedBall y ε
  proof: by
  simp [IsCover, SetRel.IsCover, subset_def]

alias ⟨IsCover.subset_iUnion_closedBall, IsCover.of_subset_iUnion_closedBall⟩ :=
  isCover_iff_subset_iUnion_closedBall

中文:
引理 isCover_iff_subset_iUnion_closedBall
  结论: IsCover ε s N ↔ s subseteq ⋃ y in N, closedBall y ε
  证明: by
  simp [IsCover, SetRel.IsCover, subset_def]

alias ⟨IsCover.subset_iUnion_closedBall, IsCover.of_subset_iUnion_closedBall⟩ :=
  isCover_iff_subset_iUnion_closedBall

Depends on / 依赖: IsCover, SetRel, SetRel.IsCover, subset_def
-/
lemma isCover_iff_subset_iUnion_closedBall : IsCover ε s N ↔ s subseteq ⋃ y in N, closedBall y ε := by
  simp [IsCover, SetRel.IsCover, subset_def]

alias ⟨IsCover.subset_iUnion_closedBall, IsCover.of_subset_iUnion_closedBall⟩ :=
  isCover_iff_subset_iUnion_closedBall

/--
lemma `IsCover.of_subset_cthickening_of_lt` / 引理 `IsCover.of_subset_cthickening_of_lt`

English:
lemma IsCover.of_subset_cthickening_of_lt
  given: {δ : Real>=0} (hsN : s subseteq cthickening ε N) (hεδ : ε < δ)
  proof: .of_subset_iUnion_closedBall hsN.trans (cthickening_subset_iUnion_closedBall_of_lt _
    (NNReal.zero_le_coe.trans_lt hεδ) hεδ)

中文:
引理 IsCover.of_subset_cthickening_of_lt
  条件: {δ : 实数>=0} (hsN : s subseteq cthickening ε N) (hεδ : ε < δ)
  证明: .of_subset_iUnion_closedBall hsN.trans (cthickening_subset_iUnion_closedBall_of_lt _
    (NNReal.zero_le_coe.trans_lt hεδ) hεδ)

Depends on / 依赖: NNReal, NNReal.zero_le_coe.trans_lt, cthickening_subset_iUnion_closedBall_of_lt, hsN.trans, of_subset_iUnion_closedBall, trans_lt, zero_le_coe
-/
lemma IsCover.of_subset_cthickening_of_lt {δ : Real>=0} (hsN : s subseteq cthickening ε N) (hεδ : ε < δ) :
    IsCover δ s N :=
.of_subset_iUnion_closedBall hsN.trans (cthickening_subset_iUnion_closedBall_of_lt _
    (NNReal.zero_le_coe.trans_lt hεδ) hεδ)

variable [ProperSpace X]

/--
lemma `isCover_iff_subset_cthickening` / 引理 `isCover_iff_subset_cthickening`

English:
lemma isCover_iff_subset_cthickening
  given: (hN : IsClosed N)
  statement: IsCover ε s N ↔ s subseteq cthickening ε N
  proof: by
  rw [isCover_iff_subset_iUnion_closedBall]; rw [hN.cthickening_eq_biUnion_closedBall ε.zero_le_coe]

alias ⟨IsCover.subset_cthickening, IsCover.of_subset_cthickening⟩ := isCover_iff_subset_cthickening

中文:
引理 isCover_iff_subset_cthickening
  条件: (hN : 是闭集 N)
  结论: IsCover ε s N ↔ s subseteq cthickening ε N
  证明: by
  rw [isCover_iff_subset_iUnion_closedBall]; rw [hN.cthickening_eq_biUnion_closedBall ε.zero_le_coe]

alias ⟨IsCover.subset_cthickening, IsCover.of_subset_cthickening⟩ := isCover_iff_subset_cthickening

Depends on / 依赖: cthickening_eq_biUnion_closedBall, hN.cthickening_eq_biUnion_closedBall, isCover_iff_subset_iUnion_closedBall, zero_le_coe
-/
lemma isCover_iff_subset_cthickening (hN : IsClosed N) : IsCover ε s N ↔ s subseteq cthickening ε N := by
  rw [isCover_iff_subset_iUnion_closedBall]; rw [hN.cthickening_eq_biUnion_closedBall ε.zero_le_coe]

alias ⟨IsCover.subset_cthickening, IsCover.of_subset_cthickening⟩ := isCover_iff_subset_cthickening

/--
lemma `isCover_closure` / 引理 `isCover_closure`

English:
lemma isCover_closure
  given: (hN : IsClosed N)
  statement: IsCover ε (closure s) N ↔ IsCover ε s N
  proof: by
  simpa [isCover_iff_subset_cthickening hN] using (isClosed_cthickening (E := N)).closure_subset_iff

protected alias ⟨_, IsCover.closure⟩ := isCover_closure

中文:
引理 isCover_closure
  条件: (hN : 是闭集 N)
  结论: IsCover ε (closure s) N ↔ IsCover ε s N
  证明: by
  simpa [isCover_iff_subset_cthickening hN] using (isClosed_cthickening (E := N)).closure_subset_iff

protected alias ⟨_, IsCover.closure⟩ := isCover_closure
-/
@[simp] lemma isCover_closure (hN : IsClosed N) : IsCover ε (closure s) N ↔ IsCover ε s N := by
  simpa [isCover_iff_subset_cthickening hN] using (isClosed_cthickening (E := N)).closure_subset_iff

protected alias ⟨_, IsCover.closure⟩ := isCover_closure

end PseudoMetricSpace

section EMetricSpace
variable [EMetricSpace X] {ε : Real>=0} {s N : Set X} {x : X}

/--
lemma `isCover_zero` / 引理 `isCover_zero`

English:
lemma isCover_zero
  statement: IsCover 0 s N ↔ s subseteq N
  proof: by
  simp [isCover_iff_subset_iUnion_closedEBall]

中文:
引理 isCover_zero
  结论: IsCover 0 s N ↔ s subseteq N
  证明: by
  simp [isCover_iff_subset_iUnion_closedEBall]
-/
@[simp] lemma isCover_zero : IsCover 0 s N ↔ s subseteq N := by
  simp [isCover_iff_subset_iUnion_closedEBall]

end EMetricSpace

section MetricSpace
variable [MetricSpace X] [ProperSpace X] {ε : Real>=0} {s t N N₁ N₂ : Set X} {x : X}

/--
lemma `IsCover.isCompact` / 引理 `IsCover.isCompact`

English:
lemma IsCover.isCompact
  given: (hsN : IsCover ε s N) (hs : IsClosed s) (hN : IsCompact N)
  proof: .of_isClosed_subset hN.cthickening hs hsN.subset_cthickening hN.isClosed

中文:
引理 IsCover.isCompact
  条件: (hsN : IsCover ε s N) (hs : 是闭集 s) (hN : 是紧集 N)
  证明: .of_isClosed_subset hN.cthickening hs hsN.subset_cthickening hN.isClosed

Depends on / 依赖: cthickening, hN.cthickening, hN.isClosed, hsN.subset_cthickening, isClosed, of_isClosed_subset, subset_cthickening
-/
lemma IsCover.isCompact (hsN : IsCover ε s N) (hs : IsClosed s) (hN : IsCompact N) :
IsCompact s := .of_isClosed_subset hN.cthickening hs hsN.subset_cthickening hN.isClosed

/--
lemma `IsCover.isCompact_closure` / 引理 `IsCover.isCompact_closure`

English:
lemma IsCover.isCompact_closure
  given: (hsN : IsCover ε s N) (hN : IsCompact N)
  proof: (hsN.closure hN.isClosed).isCompact isClosed_closure hN

中文:
引理 IsCover.isCompact_closure
  条件: (hsN : IsCover ε s N) (hN : 是紧集 N)
  证明: (hsN.closure hN.isClosed).isCompact isClosed_closure hN

Depends on / 依赖: closure, hN.isClosed, hsN.closure, isClosed, isClosed_closure, isCompact
-/
lemma IsCover.isCompact_closure (hsN : IsCover ε s N) (hN : IsCompact N) :
    IsCompact (closure s) := (hsN.closure hN.isClosed).isCompact isClosed_closure hN

/--
lemma `isCompact_closure_iff_exists_finite_isCover` / 引理 `isCompact_closure_iff_exists_finite_isCover`

English:
lemma isCompact_closure_iff_exists_finite_isCover
  given: (hε : ε != 0)
  proof: exists_finite_isCover_of_isCompact_closure hε
  mpr := fun ⟨_N, _, hN, hsN⟩ => hsN.isCompact_closure hN.isCompact

中文:
引理 isCompact_closure_iff_存在_finite_isCover
  条件: (hε : ε != 0)
  证明: exists_finite_isCover_of_isCompact_closure hε
  mpr := fun ⟨_N, _, hN, hsN⟩ => hsN.isCompact_closure hN.isCompact

Depends on / 依赖: exists_finite_isCover_of_isCompact_closure
-/
lemma isCompact_closure_iff_exists_finite_isCover (hε : ε != 0) :
    IsCompact (closure s) ↔ exists N subseteq s, N.Finite ∧ IsCover ε s N where
  mp := exists_finite_isCover_of_isCompact_closure hε
  mpr := fun ⟨_N, _, hN, hsN⟩ => hsN.isCompact_closure hN.isCompact

end MetricSpace
end Metric
