/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact sets and compact spaces and locally finite functions
-/

@[expose] public section

open Set

variable {X ι : Type*} [TopologicalSpace X] {s : Set X}

namespace LocallyFinite

/--
theorem `finite_nonempty_inter_compact` / 定理 `finite_nonempty_inter_compact`

English:
theorem finite_nonempty_inter_compact
  statement: {f : ι -> Set X}
  proof: by
  choose U hxU hUf using hf
  rcases hs.elim_nhds_subcover U fun x _ => hxU x with ⟨t, -, hsU⟩
  refine (t.finite_toSet.biUnion fun x _ => hUf x).subset ?_
  rintro i ⟨x, hx⟩
  rcases mem_iUnion₂.1 (hsU hx.2) with ⟨c, hct, hcx⟩
  exact mem_biUnion hct ⟨x, hx.1, hcx⟩

中文:
定理 finite_nonempty_inter_compact
  结论: {f : ι -> 集合 X}
  证明: by
  choose U hxU hUf using hf
  rcases hs.elim_nhds_subcover U fun x _ => hxU x with ⟨t, -, hsU⟩
  refine (t.finite_toSet.biUnion fun x _ => hUf x).subset ?_
  rintro i ⟨x, hx⟩
  rcases mem_iUnion₂.1 (hsU hx.2) with ⟨c, hct, hcx⟩
  exact mem_biUnion hct ⟨x, hx.1, hcx⟩

Depends on / 依赖: biUnion, elim_nhds_subcover, finite_toSet, hs.elim_nhds_subcover, mem_biUnion, subset, t.finite_toSet.biUnion
-/
theorem finite_nonempty_inter_compact {f : ι -> Set X}
    (hf : LocallyFinite f) (hs : IsCompact s) : { i | (f i inter s).Nonempty }.Finite := by
  choose U hxU hUf using hf
  rcases hs.elim_nhds_subcover U fun x _ => hxU x with ⟨t, -, hsU⟩
  refine (t.finite_toSet.biUnion fun x _ => hUf x).subset ?_
  rintro i ⟨x, hx⟩
  rcases mem_iUnion₂.1 (hsU hx.2) with ⟨c, hct, hcx⟩
  exact mem_biUnion hct ⟨x, hx.1, hcx⟩

/--
theorem `finite_nonempty_of_compact` / 定理 `finite_nonempty_of_compact`

English:
theorem finite_nonempty_of_compact
  statement: [CompactSpace X] {f : ι -> Set X}
  proof: by
  simpa only [inter_univ] using hf.finite_nonempty_inter_compact isCompact_univ

中文:
定理 finite_nonempty_of_compact
  结论: [紧空间 X] {f : ι -> 集合 X}
  证明: by
  simpa only [inter_univ] using hf.finite_nonempty_inter_compact isCompact_univ

Depends on / 依赖: finite_nonempty_inter_compact, hf.finite_nonempty_inter_compact, inter_univ, isCompact_univ
-/
theorem finite_nonempty_of_compact [CompactSpace X] {f : ι -> Set X}
    (hf : LocallyFinite f) : { i | (f i).Nonempty }.Finite := by
  simpa only [inter_univ] using hf.finite_nonempty_inter_compact isCompact_univ

/--
theorem `finite_of_compact` / 定理 `finite_of_compact`

English:
theorem finite_of_compact
  statement: [CompactSpace X] {f : ι -> Set X}
  proof: by
  simpa only [hne] using! hf.finite_nonempty_of_compact

中文:
定理 finite_of_compact
  结论: [紧空间 X] {f : ι -> 集合 X}
  证明: by
  simpa only [hne] using! hf.finite_nonempty_of_compact

Depends on / 依赖: finite_nonempty_of_compact, hf.finite_nonempty_of_compact
-/
theorem finite_of_compact [CompactSpace X] {f : ι -> Set X}
    (hf : LocallyFinite f) (hne : forall i, (f i).Nonempty) : (univ : Set ι).Finite := by
  simpa only [hne] using! hf.finite_nonempty_of_compact

/-- If `X` is a compact space, then a locally finite family of nonempty sets of `X` can have only
finitely many elements, `Fintype` version. -/
@[instance_reducible]
/--
Definition of `fintypeOfCompact` / `fintypeOfCompact` 的定义

English:
definition fintypeOfCompact
  signature: [CompactSpace X] {f : ι -> Set X}
  body: fintypeOfFiniteUniv (hf.finite_of_compact hne)

中文:
定义 fintypeOfCompact
  签名: [紧空间 X] {f : ι -> 集合 X}
  定义体: fintypeOfFiniteUniv (hf.finite_of_compact hne)

Depends on / 依赖: finite_of_compact, fintypeOfFiniteUniv, hf.finite_of_compact
-/
noncomputable def fintypeOfCompact [CompactSpace X] {f : ι -> Set X}
    (hf : LocallyFinite f) (hne : forall i, (f i).Nonempty) : Fintype ι :=
  fintypeOfFiniteUniv (hf.finite_of_compact hne)

end LocallyFinite
