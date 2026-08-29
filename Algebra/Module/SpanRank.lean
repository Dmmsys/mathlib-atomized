/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Xuchun Li, Christian Merten, Jingting Wang, Andrew Yang
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Minimum Cardinality of generating set of a submodule

In this file, we define the minimum cardinality of a generating set for a submodule, which is
implemented as `spanFinrank` and `spanRank`.
`spanFinrank` takes value in `ℕ` and equals `0` when no finite generating set exists.
`spanRank` takes value as a cardinal.

## Main Definitions

* `spanFinrank`: The minimum cardinality of a generating set of a submodule as a natural
  number. If no finite generating set exists, it is defined to be `0`.
* `spanRank`: The minimum cardinality of a generating set of a submodule as a cardinal.
* `FG.generators`: For a finitely generated submodule, get a set of generating elements with minimal
  cardinality.

## Main Results

* `FG.exists_span_set_card_eq_spanFinrank` : Any submodule has a generating set of cardinality equal
  to `spanRank`.

* `rank_eq_spanRank_of_free` : For a ring `R` (not necessarily commutative) satisfying
  `StrongRankCondition R`, if `M` is a free `R`-module, then the `spanRank` of `M` equals to the
  rank of M.

* `rank_le_spanRank` : For a ring `R` (not necessarily commutative) satisfying
  `StrongRankCondition R`, if `M` is an `R`-module, then the `spanRank` of `M` is less than or equal
  to the rank of M.

## Tags
submodule, generating subset, span rank

## Remark
Note that the corresponding API - `Module.rank` is only defined for a module rather than a
submodule, so there is some asymmetry here. Further refactoring might be needed if this difference
creates a friction later on.
-/

@[expose] public section

namespace Submodule

section Defs

universe u v

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

open Cardinal

/--
Definition of `spanRank` / `spanRank` 的定义

English:
definition spanRank
  signature: (p : Submodule R M)
  body: ⨅ (s : {s : Set M // span R s = p}), #s

中文:
定义 spanRank
  签名: (p : 子模 R M)
  定义体: ⨅ (s : {s : Set M // span R s = p}), #s
-/
noncomputable def spanRank (p : Submodule R M) : Cardinal := ⨅ (s : {s : Set M // span R s = p}), #s

/--
Definition of `spanFinrank` / `spanFinrank` 的定义

English:
definition spanFinrank
  signature: (p : Submodule R M)
  body: (spanRank p).toNat

中文:
定义 spanFinrank
  签名: (p : 子模 R M)
  定义体: (spanRank p).toNat

Depends on / 依赖: spanRank
-/
noncomputable def spanFinrank (p : Submodule R M) : Nat := (spanRank p).toNat

instance (p : Submodule R M) : Nonempty {s : Set M // span R s = p} := ⟨⟨p, by simp⟩⟩

/--
lemma `spanRank_toENat_eq_iInf_encard` / 引理 `spanRank_toENat_eq_iInf_encard`

English:
lemma spanRank_toENat_eq_iInf_encard
  given: (p : Submodule R M)
  statement: p.spanRank.toENat =
  proof: by
  rw [spanRank]
  apply le_antisymm
  · refine le_iInf₂ (fun s hs => ?_)
    rw [Set.encard]; rw [ENat.card]
    exact toENat.monotone' (ciInf_le' _ (⟨s, hs⟩ : {s : Set M // span R s = p}))
  · have := congrFun toENat_comp_ofENat.{u}.symm (⨅ (s : Set M) (_ : span R s = p), s.encard)
    rw [id_eq] at this; rw [this]
    refine toENat.monotone' (le_ciInf fun s => ?_)
    have : ofENat.{u} (⨅ (s' : Set M), ⨅ (_ : span R s' = p), s'.encard) <= ofENat s.1.encard :=
      ofENatHom.monotone' (le_trans (ciInf_le' _ s.1) (ciInf_le' _ s.2))
    apply le_trans this
    rw [Set.encard]; rw [ENat.card]
    exact Cardinal.ofENat_toENat_le _

中文:
引理 spanRank_toE自然数_eq_iInf_encard
  条件: (p : 子模 R M)
  结论: p.spanRank.toE自然数 =
  证明: by
  rw [spanRank]
  apply le_antisymm
  · refine le_iInf₂ (fun s hs => ?_)
    rw [Set.encard]; rw [ENat.card]
    exact toENat.monotone' (ciInf_le' _ (⟨s, hs⟩ : {s : Set M // span R s = p}))
  · have := congrFun toENat_comp_ofENat.{u}.symm (⨅ (s : Set M) (_ : span R s = p), s.encard)
    rw [id_eq] at this; rw [this]
    refine toENat.monotone' (le_ciInf fun s => ?_)
    have : ofENat.{u} (⨅ (s' : Set M), ⨅ (_ : span R s' = p), s'.encard) <= ofENat s.1.encard :=
      ofENatHom.monotone' (le_trans (ciInf_le' _ s.1) (ciInf_le' _ s.2))
    apply le_trans this
    rw [Set.encard]; rw [ENat.card]
    exact Cardinal.ofENat_toENat_le _

Depends on / 依赖: ENat.card, Set.encard, ciInf_le, encard, id_eq, le_antisymm, le_ciInf, le_trans, monotone, ofENat, ofENatHom, ofENatHom.monotone, s.encard, spanRank, toENat, toENat.monotone, toENat_comp_ofENat
-/
lemma spanRank_toENat_eq_iInf_encard (p : Submodule R M) : p.spanRank.toENat =
    (⨅ (s : Set M) (_ : span R s = p), s.encard) := by
  rw [spanRank]
  apply le_antisymm
  · refine le_iInf₂ (fun s hs => ?_)
    rw [Set.encard]; rw [ENat.card]
    exact toENat.monotone' (ciInf_le' _ (⟨s, hs⟩ : {s : Set M // span R s = p}))
  · have := congrFun toENat_comp_ofENat.{u}.symm (⨅ (s : Set M) (_ : span R s = p), s.encard)
    rw [id_eq] at this; rw [this]
    refine toENat.monotone' (le_ciInf fun s => ?_)
    have : ofENat.{u} (⨅ (s' : Set M), ⨅ (_ : span R s' = p), s'.encard) <= ofENat s.1.encard :=
      ofENatHom.monotone' (le_trans (ciInf_le' _ s.1) (ciInf_le' _ s.2))
    apply le_trans this
    rw [Set.encard]; rw [ENat.card]
    exact Cardinal.ofENat_toENat_le _

/--
lemma `spanRank_toENat_eq_iInf_finset_card` / 引理 `spanRank_toENat_eq_iInf_finset_card`

English:
lemma spanRank_toENat_eq_iInf_finset_card
  given: (p : Submodule R M)
  proof: by
  rw [spanRank_toENat_eq_iInf_encard]
  rcases eq_or_ne (⨅ (s : Set M) (_ : span R s = p), s.encard) ⊤ with (h1 | h2)
  · rw [h1, eq_comm]; simp_rw [iInf_eq_top] at h1 ⊢
    exact fun s => False.elim (Set.encard_ne_top_iff.mpr s.1.finite_toSet (h1 s.1 s.2))
  · simp_rw [← Set.encard_coe_eq_coe_finsetCard]
    apply le_antisymm
    · exact le_iInf fun s => iInf₂_le (s.1 : Set M) s.2
    · refine le_iInf fun s => le_iInf fun h => ?_
      by_cases hs : s.Finite
      · exact iInf_le_of_le ⟨hs.toFinset, by simpa⟩ (by simp)
      · rw [Set.Infinite.encard_eq hs]
        exact OrderTop.le_top _

中文:
引理 spanRank_toE自然数_eq_iInf_finset_card
  条件: (p : 子模 R M)
  证明: by
  rw [spanRank_toENat_eq_iInf_encard]
  rcases eq_or_ne (⨅ (s : Set M) (_ : span R s = p), s.encard) ⊤ with (h1 | h2)
  · rw [h1, eq_comm]; simp_rw [iInf_eq_top] at h1 ⊢
    exact fun s => False.elim (Set.encard_ne_top_iff.mpr s.1.finite_toSet (h1 s.1 s.2))
  · simp_rw [← Set.encard_coe_eq_coe_finsetCard]
    apply le_antisymm
    · exact le_iInf fun s => iInf₂_le (s.1 : Set M) s.2
    · refine le_iInf fun s => le_iInf fun h => ?_
      by_cases hs : s.Finite
      · exact iInf_le_of_le ⟨hs.toFinset, by simpa⟩ (by simp)
      · rw [Set.Infinite.encard_eq hs]
        exact OrderTop.le_top _

Depends on / 依赖: False.elim, Finite, Set.encard_coe_eq_coe_finsetCard, Set.encard_ne_top_iff.mpr, encard, encard_coe_eq_coe_finsetCard, encard_ne_top_iff, eq_comm, eq_or_ne, finite_toSet, hs.toFinset, iInf_eq_top, iInf_le_of_le, le_antisymm, le_iInf, s.Finite, s.encard, simp_rw, spanRank_toENat_eq_iInf_encard, toFinset
-/
lemma spanRank_toENat_eq_iInf_finset_card (p : Submodule R M) :
    p.spanRank.toENat = ⨅ (s : {s : Finset M // span R s = p}), (s.1.card : Nat∞) := by
  rw [spanRank_toENat_eq_iInf_encard]
  rcases eq_or_ne (⨅ (s : Set M) (_ : span R s = p), s.encard) ⊤ with (h1 | h2)
  · rw [h1, eq_comm]; simp_rw [iInf_eq_top] at h1 ⊢
    exact fun s => False.elim (Set.encard_ne_top_iff.mpr s.1.finite_toSet (h1 s.1 s.2))
  · simp_rw [← Set.encard_coe_eq_coe_finsetCard]
    apply le_antisymm
    · exact le_iInf fun s => iInf₂_le (s.1 : Set M) s.2
    · refine le_iInf fun s => le_iInf fun h => ?_
      by_cases hs : s.Finite
      · exact iInf_le_of_le ⟨hs.toFinset, by simpa⟩ (by simp)
      · rw [Set.Infinite.encard_eq hs]
        exact OrderTop.le_top _

/--
lemma `spanFinrank_eq_iInf` / 引理 `spanFinrank_eq_iInf`

English:
lemma spanFinrank_eq_iInf
  given: (p : Submodule R M)
  proof: by
  simp [spanFinrank, Cardinal.toNat, spanRank_toENat_eq_iInf_finset_card, ENat.iInf_toNat]

中文:
引理 spanFinrank_eq_iInf
  条件: (p : 子模 R M)
  证明: by
  simp [spanFinrank, Cardinal.toNat, spanRank_toENat_eq_iInf_finset_card, ENat.iInf_toNat]

Depends on / 依赖: Cardinal, Cardinal.toNat, ENat.iInf_toNat, iInf_toNat, spanFinrank, spanRank_toENat_eq_iInf_finset_card
-/
lemma spanFinrank_eq_iInf (p : Submodule R M) :
    p.spanFinrank = ⨅ (s : {s : Finset M // span R s = p}), s.1.card := by
  simp [spanFinrank, Cardinal.toNat, spanRank_toENat_eq_iInf_finset_card, ENat.iInf_toNat]

/-- A submodule's `spanRank` is finite if and only if it is finitely generated. -/
@[simp]
/--
lemma `spanRank_finite_iff_fg` / 引理 `spanRank_finite_iff_fg`

English:
lemma spanRank_finite_iff_fg
  given: {p : Submodule R M}
  statement: p.spanRank < aleph0 ↔ p.FG
  proof: by
  rw [spanRank]; rw [Submodule.fg_def]
  constructor
  · rintro h
    obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s in
      Set.range (fun (s : {s : Set M // span R s = p}) => #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
    refine ⟨s.1, ?_, s.2⟩
    simpa [← hs] using h
  · rintro ⟨s, hs₁, hs₂⟩
    exact (ciInf_le' _ ⟨s, hs₂⟩).trans_lt (by simpa)

中文:
引理 spanRank_finite_iff_fg
  条件: {p : 子模 R M}
  结论: p.spanRank < aleph0 ↔ p.FG
  证明: by
  rw [spanRank]; rw [Submodule.fg_def]
  constructor
  · rintro h
    obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s in
      Set.range (fun (s : {s : Set M // span R s = p}) => #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
    refine ⟨s.1, ?_, s.2⟩
    simpa [← hs] using h
  · rintro ⟨s, hs₁, hs₂⟩
    exact (ciInf_le' _ ⟨s, hs₂⟩).trans_lt (by simpa)

Depends on / 依赖: Set.range, Submodule, Submodule.fg_def, ciInf_le, csInf_mem, fg_def, spanRank, trans_lt
-/
lemma spanRank_finite_iff_fg {p : Submodule R M} : p.spanRank < aleph0 ↔ p.FG := by
  rw [spanRank]; rw [Submodule.fg_def]
  constructor
  · rintro h
    obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s in
      Set.range (fun (s : {s : Set M // span R s = p}) => #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
    refine ⟨s.1, ?_, s.2⟩
    simpa [← hs] using h
  · rintro ⟨s, hs₁, hs₂⟩
    exact (ciInf_le' _ ⟨s, hs₂⟩).trans_lt (by simpa)

/--
lemma `spanFinrank_of_not_fg` / 引理 `spanFinrank_of_not_fg`

English:
lemma spanFinrank_of_not_fg
  given: {p : Submodule R M} (hp : ¬p.FG)
  statement: p.spanFinrank = 0
  proof: by
  refine toNat_eq_zero.2 ?_
  right
  by_contra! h
  exact hp (spanRank_finite_iff_fg.1 h)

中文:
引理 spanFinrank_of_not_fg
  条件: {p : 子模 R M} (hp : ¬p.FG)
  结论: p.spanFinrank = 0
  证明: by
  refine toNat_eq_zero.2 ?_
  right
  by_contra! h
  exact hp (spanRank_finite_iff_fg.1 h)

Depends on / 依赖: spanRank_finite_iff_fg, toNat_eq_zero
-/
lemma spanFinrank_of_not_fg {p : Submodule R M} (hp : ¬p.FG) : p.spanFinrank = 0 := by
  refine toNat_eq_zero.2 ?_
  right
  by_contra! h
  exact hp (spanRank_finite_iff_fg.1 h)

/--
lemma `fg_iff_spanRank_eq_spanFinrank` / 引理 `fg_iff_spanRank_eq_spanFinrank`

English:
lemma fg_iff_spanRank_eq_spanFinrank
  given: {p : Submodule R M}
  statement: p.spanRank = p.spanFinrank ↔ p.FG
  proof: by
  rw [spanFinrank]; rw [← spanRank_finite_iff_fg]; rw [eq_comm]
  exact cast_toNat_eq_iff_lt_aleph0

中文:
引理 fg_iff_spanRank_eq_spanFinrank
  条件: {p : 子模 R M}
  结论: p.spanRank = p.spanFinrank ↔ p.FG
  证明: by
  rw [spanFinrank]; rw [← spanRank_finite_iff_fg]; rw [eq_comm]
  exact cast_toNat_eq_iff_lt_aleph0

Depends on / 依赖: cast_toNat_eq_iff_lt_aleph0, eq_comm, spanFinrank, spanRank_finite_iff_fg
-/
lemma fg_iff_spanRank_eq_spanFinrank {p : Submodule R M} : p.spanRank = p.spanFinrank ↔ p.FG := by
  rw [spanFinrank]; rw [← spanRank_finite_iff_fg]; rw [eq_comm]
  exact cast_toNat_eq_iff_lt_aleph0

/--
lemma `FG.spanRank_eq_spanFinrank` / 引理 `FG.spanRank_eq_spanFinrank`

English:
lemma FG.spanRank_eq_spanFinrank
  given: {p : Submodule R M} (fg : p.FG)
  statement: p.spanRank = p.spanFinrank
  proof: fg_iff_spanRank_eq_spanFinrank.mpr fg

中文:
引理 FG.spanRank_eq_spanFinrank
  条件: {p : 子模 R M} (fg : p.FG)
  结论: p.spanRank = p.spanFinrank
  证明: fg_iff_spanRank_eq_spanFinrank.mpr fg

Depends on / 依赖: fg_iff_spanRank_eq_spanFinrank, fg_iff_spanRank_eq_spanFinrank.mpr
-/
lemma FG.spanRank_eq_spanFinrank {p : Submodule R M} (fg : p.FG) : p.spanRank = p.spanFinrank :=
  fg_iff_spanRank_eq_spanFinrank.mpr fg

/--
lemma `FG.spanRank_le_iff` / 引理 `FG.spanRank_le_iff`

English:
lemma FG.spanRank_le_iff
  given: {p : Submodule R M} (hp : p.FG) (n : Nat)
  proof: (Cardinal.toNat_le_iff_of_lt_aleph0 n (by simpa)).symm

中文:
引理 FG.spanRank_le_iff
  条件: {p : 子模 R M} (hp : p.FG) (n : 自然数)
  证明: (Cardinal.toNat_le_iff_of_lt_aleph0 n (by simpa)).symm

Depends on / 依赖: Cardinal, Cardinal.toNat_le_iff_of_lt_aleph0, toNat_le_iff_of_lt_aleph0
-/
lemma FG.spanRank_le_iff {p : Submodule R M} (hp : p.FG) (n : Nat) :
    p.spanRank <= n ↔ p.spanFinrank <= n :=
  (Cardinal.toNat_le_iff_of_lt_aleph0 n (by simpa)).symm

/--
lemma `FG.spanRank_eq_iff` / 引理 `FG.spanRank_eq_iff`

English:
lemma FG.spanRank_eq_iff
  given: {p : Submodule R M} (hp : p.FG) (n : Nat)
  proof: (Cardinal.toNat_eq_iff_of_lt_aleph0 n (by simpa)).symm

中文:
引理 FG.spanRank_eq_iff
  条件: {p : 子模 R M} (hp : p.FG) (n : 自然数)
  证明: (Cardinal.toNat_eq_iff_of_lt_aleph0 n (by simpa)).symm

Depends on / 依赖: Cardinal, Cardinal.toNat_eq_iff_of_lt_aleph0, toNat_eq_iff_of_lt_aleph0
-/
lemma FG.spanRank_eq_iff {p : Submodule R M} (hp : p.FG) (n : Nat) :
    p.spanRank = n ↔ p.spanFinrank = n :=
  (Cardinal.toNat_eq_iff_of_lt_aleph0 n (by simpa)).symm

/--
lemma `spanRank_span_le_card` / 引理 `spanRank_span_le_card`

English:
lemma spanRank_span_le_card
  given: (s : Set M)
  statement: (Submodule.span R s).spanRank <= #s
  proof: by
  rw [spanRank]
  let s' : {s1 : Set M // span R s1 = span R s} := ⟨s, rfl⟩
  exact ciInf_le' _ s'

中文:
引理 spanRank_span_le_card
  条件: (s : 集合 M)
  结论: (子模.span R s).spanRank <= #s
  证明: by
  rw [spanRank]
  let s' : {s1 : Set M // span R s1 = span R s} := ⟨s, rfl⟩
  exact ciInf_le' _ s'

Depends on / 依赖: ciInf_le, spanRank
-/
lemma spanRank_span_le_card (s : Set M) : (Submodule.span R s).spanRank <= #s := by
  rw [spanRank]
  let s' : {s1 : Set M // span R s1 = span R s} := ⟨s, rfl⟩
  exact ciInf_le' _ s'

/--
lemma `spanRank_span_range_of_linearIndependent` / 引理 `spanRank_span_range_of_linearIndependent`

English:
lemma spanRank_span_range_of_linearIndependent
  statement: [RankCondition R] {ι : Type u} {v : ι -> M}
  proof: by
  refine le_antisymm (le_trans (spanRank_span_le_card _) mk_range_le) (le_ciInf fun x => ?_)
  have : #x.1 = #((Subtype.val : span R (.range v) -> _) ⁻¹' x.1) :=
    (mk_preimage_of_injective_of_subset_range _ _ Subtype.val_injective (by simp [← x.2])).symm
  rw [this]
  refine le_trans ?_ ((Module.Basis.span hs).le_span (R := R) (J := Subtype.val ⁻¹' x.1) ?_)
  · rw [mk_range_eq]
    exact .of_comp (f := Subtype.val) (by convert! hv; ext; simp [Module.Basis.span_apply])
  · apply map_injective_of_injective (f := (span R _).subtype) (injective_subtype _)
    simp [map_span, Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left, ← x.2]

中文:
引理 spanRank_span_range_of_linearIndependent
  结论: [RankCondition R] {ι : 类型u} {v : ι -> M}
  证明: by
  refine le_antisymm (le_trans (spanRank_span_le_card _) mk_range_le) (le_ciInf fun x => ?_)
  have : #x.1 = #((Subtype.val : span R (.range v) -> _) ⁻¹' x.1) :=
    (mk_preimage_of_injective_of_subset_range _ _ Subtype.val_injective (by simp [← x.2])).symm
  rw [this]
  refine le_trans ?_ ((Module.Basis.span hs).le_span (R := R) (J := Subtype.val ⁻¹' x.1) ?_)
  · rw [mk_range_eq]
    exact .of_comp (f := Subtype.val) (by convert! hv; ext; simp [Module.Basis.span_apply])
  · apply map_injective_of_injective (f := (span R _).subtype) (injective_subtype _)
    simp [map_span, Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left, ← x.2]

Depends on / 依赖: Module, Module.Basis.span, Module.Basis.span_apply, Subtype, Subtype.val, Subtype.val_injective, convert, le_antisymm, le_ciInf, le_span, le_trans, map_injective_of_injective, mk_preimage_of_injective_of_subset_range, mk_range_eq, mk_range_le, of_comp, spanRank_span_le_card, span_apply, val_injective
-/
lemma spanRank_span_range_of_linearIndependent [RankCondition R] {ι : Type u} {v : ι -> M}
    (hv : v.Injective) (hs : LinearIndependent R v) :
    (span R (.range v)).spanRank = #ι := by
  refine le_antisymm (le_trans (spanRank_span_le_card _) mk_range_le) (le_ciInf fun x => ?_)
  have : #x.1 = #((Subtype.val : span R (.range v) -> _) ⁻¹' x.1) :=
    (mk_preimage_of_injective_of_subset_range _ _ Subtype.val_injective (by simp [← x.2])).symm
  rw [this]
  refine le_trans ?_ ((Module.Basis.span hs).le_span (R := R) (J := Subtype.val ⁻¹' x.1) ?_)
  · rw [mk_range_eq]
    exact .of_comp (f := Subtype.val) (by convert! hv; ext; simp [Module.Basis.span_apply])
  · apply map_injective_of_injective (f := (span R _).subtype) (injective_subtype _)
    simp [map_span, Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left, ← x.2]

/--
lemma `spanRank_span_of_linearIndepOn` / 引理 `spanRank_span_of_linearIndepOn`

English:
lemma spanRank_span_of_linearIndepOn
  given: [RankCondition R] (s : Set M) (hs : LinearIndepOn R id s)
  proof: by
  simp [← spanRank_span_range_of_linearIndependent Subtype.val_injective hs]

中文:
引理 spanRank_span_of_linearIndepOn
  条件: [RankCondition R] (s : 集合 M) (hs : LinearIndepOn R id s)
  证明: by
  simp [← spanRank_span_range_of_linearIndependent Subtype.val_injective hs]

Depends on / 依赖: Subtype, Subtype.val_injective, spanRank_span_range_of_linearIndependent, val_injective
-/
lemma spanRank_span_of_linearIndepOn [RankCondition R] (s : Set M) (hs : LinearIndepOn R id s) :
    (span R s).spanRank = #s := by
  simp [← spanRank_span_range_of_linearIndependent Subtype.val_injective hs]

/--
lemma `spanFinrank_span_le_encard` / 引理 `spanFinrank_span_le_encard`

English:
lemma spanFinrank_span_le_encard
  given: (s : Set M)
  statement: (span R s).spanFinrank <= s.encard
  proof: by
  rw [spanFinrank]; rw [Set.encard]; rw [ENat.card]
  exact le_trans (by simp) (toENat.monotone' (spanRank_span_le_card (R := R) s))

中文:
引理 spanFinrank_span_le_encard
  条件: (s : 集合 M)
  结论: (span R s).spanFinrank <= s.encard
  证明: by
  rw [spanFinrank]; rw [Set.encard]; rw [ENat.card]
  exact le_trans (by simp) (toENat.monotone' (spanRank_span_le_card (R := R) s))

Depends on / 依赖: ENat.card, Set.encard, encard, le_trans, monotone, spanFinrank, spanRank_span_le_card, toENat, toENat.monotone
-/
lemma spanFinrank_span_le_encard (s : Set M) : (span R s).spanFinrank <= s.encard := by
  rw [spanFinrank]; rw [Set.encard]; rw [ENat.card]
  exact le_trans (by simp) (toENat.monotone' (spanRank_span_le_card (R := R) s))

/--
lemma `spanFinrank_span_le_ncard_of_finite` / 引理 `spanFinrank_span_le_ncard_of_finite`

English:
lemma spanFinrank_span_le_ncard_of_finite
  given: {s : Set M} (hs : s.Finite)
  proof: by
  rw [← Nat.cast_le (α := Nat∞)]
  exact le_trans (spanFinrank_span_le_encard _) hs.cast_ncard_eq.ge

中文:
引理 spanFinrank_span_le_ncard_of_finite
  条件: {s : 集合 M} (hs : s.有限)
  证明: by
  rw [← Nat.cast_le (α := Nat∞)]
  exact le_trans (spanFinrank_span_le_encard _) hs.cast_ncard_eq.ge

Depends on / 依赖: Nat.cast_le, cast_le, cast_ncard_eq, hs.cast_ncard_eq.ge, le_trans, spanFinrank_span_le_encard
-/
lemma spanFinrank_span_le_ncard_of_finite {s : Set M} (hs : s.Finite) :
    (span R s).spanFinrank <= s.ncard := by
  rw [← Nat.cast_le (α := Nat∞)]
  exact le_trans (spanFinrank_span_le_encard _) hs.cast_ncard_eq.ge

/--
theorem `exists_span_set_card_eq_spanRank` / 定理 `exists_span_set_card_eq_spanRank`

English:
theorem exists_span_set_card_eq_spanRank
  given: (p : Submodule R M)
  proof: by
  rw [spanRank]
  obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s in
    Set.range (fun (s : {s : Set M // span R s = p}) => #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
  exact ⟨s.1, ⟨hs, s.2⟩⟩

中文:
定理 存在_span_set_card_eq_spanRank
  条件: (p : 子模 R M)
  证明: by
  rw [spanRank]
  obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s in
    Set.range (fun (s : {s : Set M // span R s = p}) => #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
  exact ⟨s.1, ⟨hs, s.2⟩⟩

Depends on / 依赖: Set.range, csInf_mem, spanRank
-/
theorem exists_span_set_card_eq_spanRank (p : Submodule R M) :
    exists s : Set M, #s = p.spanRank ∧ span R s = p := by
  rw [spanRank]
  obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s in
    Set.range (fun (s : {s : Set M // span R s = p}) => #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
  exact ⟨s.1, ⟨hs, s.2⟩⟩

/--
theorem `FG.exists_span_set_encard_eq_spanFinrank` / 定理 `FG.exists_span_set_encard_eq_spanFinrank`

English:
theorem FG.exists_span_set_encard_eq_spanFinrank
  given: {p : Submodule R M} (h : p.FG)
  proof: by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
  refine ⟨s, ⟨?_, hs₂⟩⟩
  have := fg_iff_spanRank_eq_spanFinrank.mpr h
  rw [Set.encard]; rw [ENat.card]; rw [spanFinrank]; rw [hs₁]; rw [this]
  simp

中文:
定理 FG.存在_span_set_encard_eq_spanFinrank
  条件: {p : 子模 R M} (h : p.FG)
  证明: by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
  refine ⟨s, ⟨?_, hs₂⟩⟩
  have := fg_iff_spanRank_eq_spanFinrank.mpr h
  rw [Set.encard]; rw [ENat.card]; rw [spanFinrank]; rw [hs₁]; rw [this]
  simp

Depends on / 依赖: ENat.card, Set.encard, encard, exists_span_set_card_eq_spanRank, fg_iff_spanRank_eq_spanFinrank, fg_iff_spanRank_eq_spanFinrank.mpr, spanFinrank
-/
theorem FG.exists_span_set_encard_eq_spanFinrank {p : Submodule R M} (h : p.FG) :
    exists s : Set M, s.encard = p.spanFinrank ∧ span R s = p := by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
  refine ⟨s, ⟨?_, hs₂⟩⟩
  have := fg_iff_spanRank_eq_spanFinrank.mpr h
  rw [Set.encard]; rw [ENat.card]; rw [spanFinrank]; rw [hs₁]; rw [this]
  simp

/--
theorem `FG.exists_span_finset_card_eq_spanFinrank` / 定理 `FG.exists_span_finset_card_eq_spanFinrank`

English:
theorem FG.exists_span_finset_card_eq_spanFinrank
  given: {p : Submodule R M} (h : p.FG)
  proof: by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_encard_eq_spanFinrank h
  have s_f := Set.finite_of_encard_eq_coe hs₁
  refine ⟨s_f.toFinset, ⟨?_, by simpa using hs₂⟩⟩
  simpa [s_f.encard_eq_coe_toFinset_card, ENat.natCast_inj] using hs₁

中文:
定理 FG.存在_span_finset_card_eq_spanFinrank
  条件: {p : 子模 R M} (h : p.FG)
  证明: by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_encard_eq_spanFinrank h
  have s_f := Set.finite_of_encard_eq_coe hs₁
  refine ⟨s_f.toFinset, ⟨?_, by simpa using hs₂⟩⟩
  simpa [s_f.encard_eq_coe_toFinset_card, ENat.natCast_inj] using hs₁

Depends on / 依赖: ENat.natCast_inj, Set.finite_of_encard_eq_coe, encard_eq_coe_toFinset_card, exists_span_set_encard_eq_spanFinrank, finite_of_encard_eq_coe, natCast_inj, s_f.encard_eq_coe_toFinset_card, s_f.toFinset, toFinset
-/
theorem FG.exists_span_finset_card_eq_spanFinrank {p : Submodule R M} (h : p.FG) :
    exists s : Finset M, s.card = p.spanFinrank ∧ span R s = p := by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_encard_eq_spanFinrank h
  have s_f := Set.finite_of_encard_eq_coe hs₁
  refine ⟨s_f.toFinset, ⟨?_, by simpa using hs₂⟩⟩
  simpa [s_f.encard_eq_coe_toFinset_card, ENat.natCast_inj] using hs₁

/--
lemma `lift_spanRank_le_iff_exists_span_set_card_le` / 引理 `lift_spanRank_le_iff_exists_span_set_card_le`

English:
lemma lift_spanRank_le_iff_exists_span_set_card_le
  given: (p : Submodule R M) {a : Cardinal.{max u v}}
  proof: by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
    exact ⟨s, ⟨hs₁ ▸ h, hs₂⟩⟩
  · exact fun ⟨s, ⟨h₁, h₂⟩⟩ => h₂.symm ▸ (Cardinal.lift_le.mpr (spanRank_span_le_card s)).trans h₁

中文:
引理 lift_spanRank_le_iff_存在_span_set_card_le
  条件: (p : 子模 R M) {a : 基数.{最大值 u v}}
  证明: by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
    exact ⟨s, ⟨hs₁ ▸ h, hs₂⟩⟩
  · exact fun ⟨s, ⟨h₁, h₂⟩⟩ => h₂.symm ▸ (Cardinal.lift_le.mpr (spanRank_span_le_card s)).trans h₁

Depends on / 依赖: Cardinal, Cardinal.lift_le.mpr, exists_span_set_card_eq_spanRank, lift_le, spanRank_span_le_card
-/
lemma lift_spanRank_le_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal.{max u v}} :
    Cardinal.lift.{v} p.spanRank <= a ↔ exists s : Set M, Cardinal.lift.{v} #s <= a ∧ span R s = p := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
    exact ⟨s, ⟨hs₁ ▸ h, hs₂⟩⟩
  · exact fun ⟨s, ⟨h₁, h₂⟩⟩ => h₂.symm ▸ (Cardinal.lift_le.mpr (spanRank_span_le_card s)).trans h₁

/--
lemma `FG.spanRank_le_iff_exists_span_set_card_le` / 引理 `FG.spanRank_le_iff_exists_span_set_card_le`

English:
lemma FG.spanRank_le_iff_exists_span_set_card_le
  given: (p : Submodule R M) {a : Cardinal}
  proof: by
  convert! lift_spanRank_le_iff_exists_span_set_card_le p (a := a) <;> simp

@[simp]

中文:
引理 FG.spanRank_le_iff_存在_span_set_card_le
  条件: (p : 子模 R M) {a : 基数}
  证明: by
  convert! lift_spanRank_le_iff_exists_span_set_card_le p (a := a) <;> simp

@[simp]

Depends on / 依赖: convert, lift_spanRank_le_iff_exists_span_set_card_le
-/
lemma FG.spanRank_le_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal} :
    p.spanRank <= a ↔ exists s : Set M, #s <= a ∧ span R s = p := by
  convert! lift_spanRank_le_iff_exists_span_set_card_le p (a := a) <;> simp

@[simp]
/--
lemma `spanRank_eq_zero_iff_eq_bot` / 引理 `spanRank_eq_zero_iff_eq_bot`

English:
lemma spanRank_eq_zero_iff_eq_bot
  given: {I : Submodule R M}
  statement: I.spanRank = 0 ↔ I = ⊥
  proof: by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ :=
      (FG.spanRank_le_iff_exists_span_set_card_le I (a := 0)).mp (by rw [h])
    simp only [nonpos_iff_eq_zero, mk_eq_zero_iff, Set.isEmpty_coe_sort] at hs₁
    simp_all
  · rintro rfl; rw [spanRank]
    exact Cardinal.iInf_eq_zero_iff.mpr (Or.inr ⟨⟨∅, by simp⟩, by simp⟩)

@[simp]

中文:
引理 spanRank_eq_zero_iff_eq_bot
  条件: {I : 子模 R M}
  结论: I.spanRank = 0 ↔ I = ⊥
  证明: by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ :=
      (FG.spanRank_le_iff_exists_span_set_card_le I (a := 0)).mp (by rw [h])
    simp only [nonpos_iff_eq_zero, mk_eq_zero_iff, Set.isEmpty_coe_sort] at hs₁
    simp_all
  · rintro rfl; rw [spanRank]
    exact Cardinal.iInf_eq_zero_iff.mpr (Or.inr ⟨⟨∅, by simp⟩, by simp⟩)

@[simp]

Depends on / 依赖: Cardinal, Cardinal.iInf_eq_zero_iff.mpr, FG.spanRank_le_iff_exists_span_set_card_le, Or.inr, Set.isEmpty_coe_sort, iInf_eq_zero_iff, isEmpty_coe_sort, mk_eq_zero_iff, nonpos_iff_eq_zero, spanRank, spanRank_le_iff_exists_span_set_card_le
-/
lemma spanRank_eq_zero_iff_eq_bot {I : Submodule R M} : I.spanRank = 0 ↔ I = ⊥ := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ :=
      (FG.spanRank_le_iff_exists_span_set_card_le I (a := 0)).mp (by rw [h])
    simp only [nonpos_iff_eq_zero, mk_eq_zero_iff, Set.isEmpty_coe_sort] at hs₁
    simp_all
  · rintro rfl; rw [spanRank]
    exact Cardinal.iInf_eq_zero_iff.mpr (Or.inr ⟨⟨∅, by simp⟩, by simp⟩)

@[simp]
/--
lemma `spanRank_bot` / 引理 `spanRank_bot`

English:
lemma spanRank_bot
  statement: (⊥ : Ideal R).spanRank = 0
  proof: Submodule.spanRank_eq_zero_iff_eq_bot.mpr rfl

@[simp]

中文:
引理 spanRank_bot
  结论: (⊥ : 理想 R).spanRank = 0
  证明: Submodule.spanRank_eq_zero_iff_eq_bot.mpr rfl

@[simp]

Depends on / 依赖: Submodule, Submodule.spanRank_eq_zero_iff_eq_bot.mpr, spanRank_eq_zero_iff_eq_bot
-/
lemma spanRank_bot : (⊥ : Ideal R).spanRank = 0 := Submodule.spanRank_eq_zero_iff_eq_bot.mpr rfl

@[simp]
/--
lemma `spanFinrank_bot` / 引理 `spanFinrank_bot`

English:
lemma spanFinrank_bot
  statement: (⊥ : Submodule R M).spanFinrank = 0
  proof: by simp [spanFinrank]

@[nontriviality]

中文:
引理 spanFinrank_bot
  结论: (⊥ : 子模 R M).spanFinrank = 0
  证明: by simp [spanFinrank]

@[nontriviality]

Depends on / 依赖: spanFinrank
-/
lemma spanFinrank_bot : (⊥ : Submodule R M).spanFinrank = 0 := by simp [spanFinrank]

@[nontriviality]
/--
lemma `spanRank_subsingleton` / 引理 `spanRank_subsingleton`

English:
lemma spanRank_subsingleton
  given: [Subsingleton R] (p : Submodule R M)
  statement: p.spanRank = 0
  proof: by
  simp [nontriviality]

@[nontriviality]

中文:
引理 spanRank_subsingleton
  条件: [子单例 R] (p : 子模 R M)
  结论: p.spanRank = 0
  证明: by
  simp [nontriviality]

@[nontriviality]

Depends on / 依赖: nontriviality
-/
lemma spanRank_subsingleton [Subsingleton R] (p : Submodule R M) : p.spanRank = 0 := by
  simp [nontriviality]

@[nontriviality]
/--
lemma `spanFinrank_subsingleton` / 引理 `spanFinrank_subsingleton`

English:
lemma spanFinrank_subsingleton
  given: [Subsingleton R] (p : Submodule R M)
  statement: p.spanFinrank = 0
  proof: by
  have := Module.subsingleton R M
  simp [Submodule.eq_bot_of_subsingleton]

中文:
引理 spanFinrank_subsingleton
  条件: [子单例 R] (p : 子模 R M)
  结论: p.spanFinrank = 0
  证明: by
  have := Module.subsingleton R M
  simp [Submodule.eq_bot_of_subsingleton]

Depends on / 依赖: Module, Module.subsingleton, Submodule, Submodule.eq_bot_of_subsingleton, eq_bot_of_subsingleton, subsingleton
-/
lemma spanFinrank_subsingleton [Subsingleton R] (p : Submodule R M) : p.spanFinrank = 0 := by
  have := Module.subsingleton R M
  simp [Submodule.eq_bot_of_subsingleton]

/--
Definition of `generators` / `generators` 的定义

English:
definition generators
  signature: (p : Submodule R M)
  body: Classical.choose (exists_span_set_card_eq_spanRank p)

中文:
定义 generators
  签名: (p : 子模 R M)
  定义体: Classical.choose (exists_span_set_card_eq_spanRank p)

Depends on / 依赖: Classical, Classical.choose, exists_span_set_card_eq_spanRank
-/
noncomputable def generators (p : Submodule R M) : Set M :=
  Classical.choose (exists_span_set_card_eq_spanRank p)

/--
lemma `generators_card` / 引理 `generators_card`

English:
lemma generators_card
  given: (p : Submodule R M)
  statement: #(generators p) = spanRank p
  proof: (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).1

中文:
引理 generators_card
  条件: (p : 子模 R M)
  结论: #(generators p) = spanRank p
  证明: (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_span_set_card_eq_spanRank
-/
lemma generators_card (p : Submodule R M) : #(generators p) = spanRank p :=
  (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).1

/--
lemma `FG.generators_ncard` / 引理 `FG.generators_ncard`

English:
lemma FG.generators_ncard
  given: {p : Submodule R M} (h : p.FG)
  proof: by
  rw [← Nat.cast_inj (R := Cardinal)]; rw [← fg_iff_spanRank_eq_spanFinrank.mpr h]; rw [Set.ncard]; rw [Set.encard]; rw [ENat.card]; rw [generators_card]; rw [toNat_toENat]; rw [← spanFinrank]
  exact (fg_iff_spanRank_eq_spanFinrank.mpr h).symm

中文:
引理 FG.generators_ncard
  条件: {p : 子模 R M} (h : p.FG)
  证明: by
  rw [← Nat.cast_inj (R := Cardinal)]; rw [← fg_iff_spanRank_eq_spanFinrank.mpr h]; rw [Set.ncard]; rw [Set.encard]; rw [ENat.card]; rw [generators_card]; rw [toNat_toENat]; rw [← spanFinrank]
  exact (fg_iff_spanRank_eq_spanFinrank.mpr h).symm

Depends on / 依赖: Cardinal, ENat.card, Nat.cast_inj, Set.encard, Set.ncard, cast_inj, encard, fg_iff_spanRank_eq_spanFinrank, fg_iff_spanRank_eq_spanFinrank.mpr, generators_card, spanFinrank, toNat_toENat
-/
lemma FG.generators_ncard {p : Submodule R M} (h : p.FG) :
    (generators p).ncard = spanFinrank p := by
  rw [← Nat.cast_inj (R := Cardinal)]; rw [← fg_iff_spanRank_eq_spanFinrank.mpr h]; rw [Set.ncard]; rw [Set.encard]; rw [ENat.card]; rw [generators_card]; rw [toNat_toENat]; rw [← spanFinrank]
  exact (fg_iff_spanRank_eq_spanFinrank.mpr h).symm

/--
lemma `FG.finite_generators` / 引理 `FG.finite_generators`

English:
lemma FG.finite_generators
  given: {p : Submodule R M} (hp : p.FG)
  proof: by
  rw [← Cardinal.lt_aleph0_iff_set_finite]; rw [Submodule.generators_card]
  exact spanRank_finite_iff_fg.mpr hp

中文:
引理 FG.finite_generators
  条件: {p : 子模 R M} (hp : p.FG)
  证明: by
  rw [← Cardinal.lt_aleph0_iff_set_finite]; rw [Submodule.generators_card]
  exact spanRank_finite_iff_fg.mpr hp

Depends on / 依赖: Cardinal, Cardinal.lt_aleph0_iff_set_finite, Submodule, Submodule.generators_card, generators_card, lt_aleph0_iff_set_finite, spanRank_finite_iff_fg, spanRank_finite_iff_fg.mpr
-/
lemma FG.finite_generators {p : Submodule R M} (hp : p.FG) :
    p.generators.Finite := by
  rw [← Cardinal.lt_aleph0_iff_set_finite]; rw [Submodule.generators_card]
  exact spanRank_finite_iff_fg.mpr hp

/--
lemma `span_generators` / 引理 `span_generators`

English:
lemma span_generators
  given: (p : Submodule R M)
  statement: span R (generators p) = p
  proof: (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).2

中文:
引理 span_generators
  条件: (p : 子模 R M)
  结论: span R (generators p) = p
  证明: (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).2

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_span_set_card_eq_spanRank
-/
lemma span_generators (p : Submodule R M) : span R (generators p) = p :=
  (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).2

/--
lemma `FG.generators_mem` / 引理 `FG.generators_mem`

English:
lemma FG.generators_mem
  given: (p : Submodule R M)
  statement: generators p subseteq p
  proof: by
  nth_rw 2 [← span_generators p]
  exact subset_span (s := generators p)

中文:
引理 FG.generators_mem
  条件: (p : 子模 R M)
  结论: generators p subseteq p
  证明: by
  nth_rw 2 [← span_generators p]
  exact subset_span (s := generators p)

Depends on / 依赖: generators, nth_rw, span_generators, subset_span
-/
lemma FG.generators_mem (p : Submodule R M) : generators p subseteq p := by
  nth_rw 2 [← span_generators p]
  exact subset_span (s := generators p)

/--
lemma `spanRank_sup_le_sum_spanRank` / 引理 `spanRank_sup_le_sum_spanRank`

English:
lemma spanRank_sup_le_sum_spanRank
  given: {p q : Submodule R M}
  proof: by
  apply (FG.spanRank_le_iff_exists_span_set_card_le (p ⊔ q)).mpr
  obtain ⟨sp, ⟨hp₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank p
  obtain ⟨sq, ⟨hq₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank q
  exact ⟨sp union sq, ⟨hp₁ ▸ hq₁ ▸ (Cardinal.mk_union_le sp sq), span_union sp sq⟩⟩

中文:
引理 spanRank_sup_le_sum_spanRank
  条件: {p q : 子模 R M}
  证明: by
  apply (FG.spanRank_le_iff_exists_span_set_card_le (p ⊔ q)).mpr
  obtain ⟨sp, ⟨hp₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank p
  obtain ⟨sq, ⟨hq₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank q
  exact ⟨sp union sq, ⟨hp₁ ▸ hq₁ ▸ (Cardinal.mk_union_le sp sq), span_union sp sq⟩⟩

Depends on / 依赖: Cardinal, Cardinal.mk_union_le, FG.spanRank_le_iff_exists_span_set_card_le, exists_span_set_card_eq_spanRank, mk_union_le, spanRank_le_iff_exists_span_set_card_le, span_union
-/
lemma spanRank_sup_le_sum_spanRank {p q : Submodule R M} :
    (p ⊔ q).spanRank <= p.spanRank + q.spanRank := by
  apply (FG.spanRank_le_iff_exists_span_set_card_le (p ⊔ q)).mpr
  obtain ⟨sp, ⟨hp₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank p
  obtain ⟨sq, ⟨hq₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank q
  exact ⟨sp union sq, ⟨hp₁ ▸ hq₁ ▸ (Cardinal.mk_union_le sp sq), span_union sp sq⟩⟩

/--
lemma `spanFinrank_eq_zero_iff_eq_bot` / 引理 `spanFinrank_eq_zero_iff_eq_bot`

English:
lemma spanFinrank_eq_zero_iff_eq_bot
  given: {p : Submodule R M} (h : p.FG)
  proof: by
  refine ⟨fun heq => ?_, fun h => by simp [h]⟩
  rw [← Submodule.FG.generators_ncard h]; rw [Set.ncard_eq_zero h.finite_generators] at heq
  rw [← p.span_generators]; rw [heq]; rw [span_empty]

中文:
引理 spanFinrank_eq_zero_iff_eq_bot
  条件: {p : 子模 R M} (h : p.FG)
  证明: by
  refine ⟨fun heq => ?_, fun h => by simp [h]⟩
  rw [← Submodule.FG.generators_ncard h]; rw [Set.ncard_eq_zero h.finite_generators] at heq
  rw [← p.span_generators]; rw [heq]; rw [span_empty]

Depends on / 依赖: Set.ncard_eq_zero, Submodule, Submodule.FG.generators_ncard, finite_generators, generators_ncard, h.finite_generators, ncard_eq_zero, p.span_generators, span_empty, span_generators
-/
lemma spanFinrank_eq_zero_iff_eq_bot {p : Submodule R M} (h : p.FG) :
    p.spanFinrank = 0 ↔ p = ⊥ := by
  refine ⟨fun heq => ?_, fun h => by simp [h]⟩
  rw [← Submodule.FG.generators_ncard h]; rw [Set.ncard_eq_zero h.finite_generators] at heq
  rw [← p.span_generators]; rw [heq]; rw [span_empty]

/--
lemma `spanFinrank_singleton` / 引理 `spanFinrank_singleton`

English:
lemma spanFinrank_singleton
  given: {m : M} (hm : m != 0)
  statement: (span R {m}).spanFinrank = 1
  proof: by
  apply le_antisymm ?_ ?_
  · exact le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (by simp)) (by simp)
  · by_contra!
    simp [Submodule.spanFinrank_eq_zero_iff_eq_bot (fg_span_singleton m), hm] at this

中文:
引理 spanFinrank_singleton
  条件: {m : M} (hm : m != 0)
  结论: (span R {m}).spanFinrank = 1
  证明: by
  apply le_antisymm ?_ ?_
  · exact le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (by simp)) (by simp)
  · by_contra!
    simp [Submodule.spanFinrank_eq_zero_iff_eq_bot (fg_span_singleton m), hm] at this

Depends on / 依赖: Submodule, Submodule.spanFinrank_eq_zero_iff_eq_bot, Submodule.spanFinrank_span_le_ncard_of_finite, fg_span_singleton, le_antisymm, le_trans, spanFinrank_eq_zero_iff_eq_bot, spanFinrank_span_le_ncard_of_finite
-/
lemma spanFinrank_singleton {m : M} (hm : m != 0) : (span R {m}).spanFinrank = 1 := by
  apply le_antisymm ?_ ?_
  · exact le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (by simp)) (by simp)
  · by_contra!
    simp [Submodule.spanFinrank_eq_zero_iff_eq_bot (fg_span_singleton m), hm] at this

/--
lemma `spanFinrank_eq_one_iff` / 引理 `spanFinrank_eq_one_iff`

English:
lemma spanFinrank_eq_one_iff
  given: (p : Submodule R M)
  statement: p.spanFinrank = 1 ↔ p.IsPrincipal ∧ p != ⊥
  proof: by
  refine ⟨fun h => ⟨?_, (by grind [spanFinrank_bot])⟩,
    fun ⟨⟨a, ha⟩, _⟩ => ha ▸ spanFinrank_singleton (by simp_all)⟩
  have fg : p.FG := spanRank_finite_iff_fg.1 (by simp_all [spanFinrank])
  obtain ⟨a, ha⟩ : exists a, p.generators = {a} := by simpa [← fg.generators_ncard] using h
  exact ⟨a, ha ▸ (p.span_generators).symm⟩

中文:
引理 spanFinrank_eq_one_iff
  条件: (p : 子模 R M)
  结论: p.spanFinrank = 1 ↔ p.是Principal ∧ p != ⊥
  证明: by
  refine ⟨fun h => ⟨?_, (by grind [spanFinrank_bot])⟩,
    fun ⟨⟨a, ha⟩, _⟩ => ha ▸ spanFinrank_singleton (by simp_all)⟩
  have fg : p.FG := spanRank_finite_iff_fg.1 (by simp_all [spanFinrank])
  obtain ⟨a, ha⟩ : exists a, p.generators = {a} := by simpa [← fg.generators_ncard] using h
  exact ⟨a, ha ▸ (p.span_generators).symm⟩

Depends on / 依赖: fg.generators_ncard, generators, generators_ncard, p.FG, p.generators, p.span_generators, spanFinrank, spanFinrank_bot, spanFinrank_singleton, spanRank_finite_iff_fg, span_generators
-/
lemma spanFinrank_eq_one_iff (p : Submodule R M) : p.spanFinrank = 1 ↔ p.IsPrincipal ∧ p != ⊥ := by
  refine ⟨fun h => ⟨?_, (by grind [spanFinrank_bot])⟩,
    fun ⟨⟨a, ha⟩, _⟩ => ha ▸ spanFinrank_singleton (by simp_all)⟩
  have fg : p.FG := spanRank_finite_iff_fg.1 (by simp_all [spanFinrank])
  obtain ⟨a, ha⟩ : exists a, p.generators = {a} := by simpa [← fg.generators_ncard] using h
  exact ⟨a, ha ▸ (p.span_generators).symm⟩

end Defs

end Submodule

section map

universe u v
namespace Submodule

section Semilinear

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R ->+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

/--
lemma `lift_spanRank_map_le` / 引理 `lift_spanRank_map_le`

English:
lemma lift_spanRank_map_le
  given: [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) (p : Submodule R M)
  proof: by
  rw [← generators_card p]; rw [lift_spanRank_le_iff_exists_span_set_card_le]
  exact ⟨f '' p.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun n ⟨m, hm, h⟩ =>
    ⟨m, span_generators p ▸ subset_span hm, h⟩)) (by simp [span_generators])⟩

中文:
引理 lift_spanRank_map_le
  条件: [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) (p : 子模 R M)
  证明: by
  rw [← generators_card p]; rw [lift_spanRank_le_iff_exists_span_set_card_le]
  exact ⟨f '' p.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun n ⟨m, hm, h⟩ =>
    ⟨m, span_generators p ▸ subset_span hm, h⟩)) (by simp [span_generators])⟩

Depends on / 依赖: Cardinal, Cardinal.mk_image_le_lift, generators, generators_card, le_antisymm, lift_spanRank_le_iff_exists_span_set_card_le, mk_image_le_lift, p.generators, span_generators, span_le, subset_span
-/
lemma lift_spanRank_map_le [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) (p : Submodule R M) :
    Cardinal.lift.{u} (p.map f).spanRank <= Cardinal.lift.{v} p.spanRank := by
  rw [← generators_card p]; rw [lift_spanRank_le_iff_exists_span_set_card_le]
  exact ⟨f '' p.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun n ⟨m, hm, h⟩ =>
    ⟨m, span_generators p ▸ subset_span hm, h⟩)) (by simp [span_generators])⟩

/--
lemma `spanRank_map_le` / 引理 `spanRank_map_le`

English:
lemma spanRank_map_le
  given: [RingHomSurjective σ] (f : M ->ₛₗ[σ] N) (p : Submodule R M)
  proof: by
  simpa using lift_spanRank_map_le f p

中文:
引理 spanRank_map_le
  条件: [RingHomSurjective σ] (f : M ->ₛₗ[σ] N) (p : 子模 R M)
  证明: by
  simpa using lift_spanRank_map_le f p

Depends on / 依赖: lift_spanRank_map_le
-/
lemma spanRank_map_le [RingHomSurjective σ] (f : M ->ₛₗ[σ] N) (p : Submodule R M) :
    (p.map f).spanRank <= p.spanRank := by
  simpa using lift_spanRank_map_le f p

/--
lemma `spanFinrank_map_le_of_fg` / 引理 `spanFinrank_map_le_of_fg`

English:
lemma spanFinrank_map_le_of_fg
  statement: [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) {p : Submodule R M}
  proof: by
  rw [← (hp.map f).spanRank_le_iff]; rw [← Cardinal.lift_le.{u}]; rw [Cardinal.lift_natCast]; rw [← Cardinal.lift_natCast.{v}]; rw [← hp.spanRank_eq_spanFinrank]
  exact p.lift_spanRank_map_le f

中文:
引理 spanFinrank_map_le_of_fg
  结论: [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) {p : 子模 R M}
  证明: by
  rw [← (hp.map f).spanRank_le_iff]; rw [← Cardinal.lift_le.{u}]; rw [Cardinal.lift_natCast]; rw [← Cardinal.lift_natCast.{v}]; rw [← hp.spanRank_eq_spanFinrank]
  exact p.lift_spanRank_map_le f

Depends on / 依赖: Cardinal, Cardinal.lift_le, Cardinal.lift_natCast, hp.map, hp.spanRank_eq_spanFinrank, lift_le, lift_natCast, lift_spanRank_map_le, p.lift_spanRank_map_le, spanRank_eq_spanFinrank, spanRank_le_iff
-/
lemma spanFinrank_map_le_of_fg [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) {p : Submodule R M}
    (hp : p.FG) : (p.map f).spanFinrank <= p.spanFinrank := by
  rw [← (hp.map f).spanRank_le_iff]; rw [← Cardinal.lift_le.{u}]; rw [Cardinal.lift_natCast]; rw [← Cardinal.lift_natCast.{v}]; rw [← hp.spanRank_eq_spanFinrank]
  exact p.lift_spanRank_map_le f

/--
lemma `lift_spanRank_map_eq_of_injective` / 引理 `lift_spanRank_map_eq_of_injective`

English:
lemma lift_spanRank_map_eq_of_injective
  statement: [RingHomSurjective σ] (f : M ->ₛₗ[σ] L)
  proof: by
  refine (lift_spanRank_map_le f p).antisymm ?_
  obtain ⟨s, hs, e⟩ := (p.map f).exists_span_set_card_eq_spanRank
  obtain ⟨s, rfl⟩ : exists y, f '' y = s := Set.subset_range_iff_exists_image_eq.mp
    ((subset_span.trans e.le).trans LinearMap.map_le_range)
  obtain rfl : span R s = p := by simpa [(map_injective_of_injective hf).eq_iff] using e
  grw [← hs, Cardinal.mk_image_eq_lift _ _ hf, Cardinal.lift_le, spanRank_span_le_card]

中文:
引理 lift_spanRank_map_eq_of_injective
  结论: [RingHomSurjective σ] (f : M ->ₛₗ[σ] L)
  证明: by
  refine (lift_spanRank_map_le f p).antisymm ?_
  obtain ⟨s, hs, e⟩ := (p.map f).exists_span_set_card_eq_spanRank
  obtain ⟨s, rfl⟩ : exists y, f '' y = s := Set.subset_range_iff_exists_image_eq.mp
    ((subset_span.trans e.le).trans LinearMap.map_le_range)
  obtain rfl : span R s = p := by simpa [(map_injective_of_injective hf).eq_iff] using e
  grw [← hs, Cardinal.mk_image_eq_lift _ _ hf, Cardinal.lift_le, spanRank_span_le_card]

Depends on / 依赖: Cardinal, Cardinal.lift_le, Cardinal.mk_image_eq_lift, LinearMap, LinearMap.map_le_range, Set.subset_range_iff_exists_image_eq.mp, antisymm, e.le, eq_iff, exists_span_set_card_eq_spanRank, lift_le, lift_spanRank_map_le, map_injective_of_injective, map_le_range, mk_image_eq_lift, p.map, spanRank_span_le_card, subset_range_iff_exists_image_eq, subset_span, subset_span.trans
-/
lemma lift_spanRank_map_eq_of_injective [RingHomSurjective σ] (f : M ->ₛₗ[σ] L)
    (hf : Function.Injective f) (p : Submodule R M) :
    Cardinal.lift.{u} (p.map f).spanRank = Cardinal.lift.{v} p.spanRank := by
  refine (lift_spanRank_map_le f p).antisymm ?_
  obtain ⟨s, hs, e⟩ := (p.map f).exists_span_set_card_eq_spanRank
  obtain ⟨s, rfl⟩ : exists y, f '' y = s := Set.subset_range_iff_exists_image_eq.mp
    ((subset_span.trans e.le).trans LinearMap.map_le_range)
  obtain rfl : span R s = p := by simpa [(map_injective_of_injective hf).eq_iff] using e
  grw [← hs, Cardinal.mk_image_eq_lift _ _ hf, Cardinal.lift_le, spanRank_span_le_card]

/--
lemma `spanRank_map_eq_of_injective` / 引理 `spanRank_map_eq_of_injective`

English:
lemma spanRank_map_eq_of_injective
  statement: [RingHomSurjective σ] (f : M ->ₛₗ[σ] N)
  proof: by
  simpa using lift_spanRank_map_eq_of_injective f hf p

中文:
引理 spanRank_map_eq_of_injective
  结论: [RingHomSurjective σ] (f : M ->ₛₗ[σ] N)
  证明: by
  simpa using lift_spanRank_map_eq_of_injective f hf p

Depends on / 依赖: lift_spanRank_map_eq_of_injective
-/
lemma spanRank_map_eq_of_injective [RingHomSurjective σ] (f : M ->ₛₗ[σ] N)
    (hf : Function.Injective f) (p : Submodule R M) : (p.map f).spanRank = p.spanRank := by
  simpa using lift_spanRank_map_eq_of_injective f hf p

/--
lemma `spanFinrank_map_eq_of_injective` / 引理 `spanFinrank_map_eq_of_injective`

English:
lemma spanFinrank_map_eq_of_injective
  statement: [RingHomSurjective σ] (f : M ->ₛₗ[σ] L)
  proof: by
  rw [Submodule.spanFinrank]; rw [Submodule.spanFinrank]; rw [← Cardinal.toNat_lift.{u]; rw [v}]; rw [← Cardinal.toNat_lift.{v]; rw [u}]; rw [lift_spanRank_map_eq_of_injective f hf p]

中文:
引理 spanFinrank_map_eq_of_injective
  结论: [RingHomSurjective σ] (f : M ->ₛₗ[σ] L)
  证明: by
  rw [Submodule.spanFinrank]; rw [Submodule.spanFinrank]; rw [← Cardinal.toNat_lift.{u]; rw [v}]; rw [← Cardinal.toNat_lift.{v]; rw [u}]; rw [lift_spanRank_map_eq_of_injective f hf p]

Depends on / 依赖: Cardinal, Cardinal.toNat_lift, Submodule, Submodule.spanFinrank, lift_spanRank_map_eq_of_injective, spanFinrank, toNat_lift
-/
lemma spanFinrank_map_eq_of_injective [RingHomSurjective σ] (f : M ->ₛₗ[σ] L)
    (hf : Function.Injective f) {p : Submodule R M} :
    (p.map f).spanFinrank = p.spanFinrank := by
  rw [Submodule.spanFinrank]; rw [Submodule.spanFinrank]; rw [← Cardinal.toNat_lift.{u]; rw [v}]; rw [← Cardinal.toNat_lift.{v]; rw [u}]; rw [lift_spanRank_map_eq_of_injective f hf p]

/--
lemma `spanRank_range_le` / 引理 `spanRank_range_le`

English:
lemma spanRank_range_le
  given: [RingHomSurjective σ] (f : M ->ₛₗ[σ] N)
  proof: by
  simpa using spanRank_map_le f ⊤

@[simp]

中文:
引理 spanRank_range_le
  条件: [RingHomSurjective σ] (f : M ->ₛₗ[σ] N)
  证明: by
  simpa using spanRank_map_le f ⊤

@[simp]

Depends on / 依赖: spanRank_map_le
-/
lemma spanRank_range_le [RingHomSurjective σ] (f : M ->ₛₗ[σ] N) :
    (LinearMap.range f).spanRank <= (⊤ : Submodule R M).spanRank := by
  simpa using spanRank_map_le f ⊤

@[simp]
/--
lemma `spanRank_top` / 引理 `spanRank_top`

English:
lemma spanRank_top
  given: (p : Submodule R M)
  statement: (⊤ : Submodule R p).spanRank = p.spanRank
  proof: by
  simpa using (spanRank_map_eq_of_injective _ p.subtype_injective ⊤).symm

中文:
引理 spanRank_top
  条件: (p : 子模 R M)
  结论: (⊤ : 子模 R p).spanRank = p.spanRank
  证明: by
  simpa using (spanRank_map_eq_of_injective _ p.subtype_injective ⊤).symm

Depends on / 依赖: p.subtype_injective, spanRank_map_eq_of_injective, subtype_injective
-/
lemma spanRank_top (p : Submodule R M) : (⊤ : Submodule R p).spanRank = p.spanRank := by
  simpa using (spanRank_map_eq_of_injective _ p.subtype_injective ⊤).symm

/--
lemma `spanFinrank_top` / 引理 `spanFinrank_top`

English:
lemma spanFinrank_top
  given: (p : Submodule R M)
  statement: (⊤ : Submodule R p).spanFinrank = p.spanFinrank
  proof: by
  simp [Submodule.spanFinrank]

中文:
引理 spanFinrank_top
  条件: (p : 子模 R M)
  结论: (⊤ : 子模 R p).spanFinrank = p.spanFinrank
  证明: by
  simp [Submodule.spanFinrank]

Depends on / 依赖: Submodule, Submodule.spanFinrank, spanFinrank
-/
lemma spanFinrank_top (p : Submodule R M) : (⊤ : Submodule R p).spanFinrank = p.spanFinrank := by
  simp [Submodule.spanFinrank]

/--
lemma `spanRank_eq_of_equiv` / 引理 `spanRank_eq_of_equiv`

English:
lemma spanRank_eq_of_equiv
  proof: by
  rw [← spanRank_map_eq_of_injective e.toLinearMap e.injective ⊤]; rw [map_top]; rw [LinearEquiv.range]

中文:
引理 spanRank_eq_of_equiv
  证明: by
  rw [← spanRank_map_eq_of_injective e.toLinearMap e.injective ⊤]; rw [map_top]; rw [LinearEquiv.range]

Depends on / 依赖: LinearEquiv, LinearEquiv.range, e.injective, e.toLinearMap, injective, map_top, spanRank_map_eq_of_injective, toLinearMap
-/
lemma spanRank_eq_of_equiv
    {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] N) : (⊤ : Submodule R M).spanRank = (⊤ : Submodule S N).spanRank := by
  rw [← spanRank_map_eq_of_injective e.toLinearMap e.injective ⊤]; rw [map_top]; rw [LinearEquiv.range]

end Semilinear

section RestrictScalars

variable {R S : Type*} {M : Type u} [CommSemiring R] [Semiring S] [AddCommMonoid M]
  [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

/--
lemma `le_spanRank_restrictScalars` / 引理 `le_spanRank_restrictScalars`

English:
lemma le_spanRank_restrictScalars
  given: (N : Submodule S M)
  proof: by
  obtain ⟨s, hs, e⟩ := (N.restrictScalars R).exists_span_set_card_eq_spanRank
  obtain rfl : span S s = N :=
    le_antisymm (span_le.mpr (span_le.mp e.le :)) (e.ge.trans (span_le_restrictScalars R S s))
  grw [← hs, spanRank_span_le_card]

中文:
引理 le_spanRank_restrictScalars
  条件: (N : 子模 S M)
  证明: by
  obtain ⟨s, hs, e⟩ := (N.restrictScalars R).exists_span_set_card_eq_spanRank
  obtain rfl : span S s = N :=
    le_antisymm (span_le.mpr (span_le.mp e.le :)) (e.ge.trans (span_le_restrictScalars R S s))
  grw [← hs, spanRank_span_le_card]

Depends on / 依赖: N.restrictScalars, e.ge.trans, e.le, exists_span_set_card_eq_spanRank, le_antisymm, restrictScalars, spanRank_span_le_card, span_le, span_le.mp, span_le.mpr, span_le_restrictScalars
-/
lemma le_spanRank_restrictScalars (N : Submodule S M) :
    N.spanRank <= (N.restrictScalars R).spanRank := by
  obtain ⟨s, hs, e⟩ := (N.restrictScalars R).exists_span_set_card_eq_spanRank
  obtain rfl : span S s = N :=
    le_antisymm (span_le.mpr (span_le.mp e.le :)) (e.ge.trans (span_le_restrictScalars R S s))
  grw [← hs, spanRank_span_le_card]

/--
lemma `spanRank_restrictScalars_eq` / 引理 `spanRank_restrictScalars_eq`

English:
lemma spanRank_restrictScalars_eq
  statement: (H : Function.Surjective (algebraMap R S))
  proof: by
  refine N.le_spanRank_restrictScalars.antisymm' ?_
  obtain ⟨s, hs, rfl⟩ := N.exists_span_set_card_eq_spanRank
  grw [restrictScalars_span R S H s, ← hs, spanRank_span_le_card]

中文:
引理 spanRank_restrictScalars_eq
  结论: (H : 函数.满射 (algebraMap R S))
  证明: by
  refine N.le_spanRank_restrictScalars.antisymm' ?_
  obtain ⟨s, hs, rfl⟩ := N.exists_span_set_card_eq_spanRank
  grw [restrictScalars_span R S H s, ← hs, spanRank_span_le_card]

Depends on / 依赖: N.exists_span_set_card_eq_spanRank, N.le_spanRank_restrictScalars.antisymm, antisymm, exists_span_set_card_eq_spanRank, le_spanRank_restrictScalars, restrictScalars_span, spanRank_span_le_card
-/
lemma spanRank_restrictScalars_eq (H : Function.Surjective (algebraMap R S))
    (N : Submodule S M) : (N.restrictScalars R).spanRank = N.spanRank := by
  refine N.le_spanRank_restrictScalars.antisymm' ?_
  obtain ⟨s, hs, rfl⟩ := N.exists_span_set_card_eq_spanRank
  grw [restrictScalars_span R S H s, ← hs, spanRank_span_le_card]

end RestrictScalars

end Submodule

section Ideal

variable {R S : Type u} [Semiring R] [Semiring S] {T : Type v} [Semiring T]

open Submodule in
/--
lemma `Ideal.lift_spanRank_map_le` / 引理 `Ideal.lift_spanRank_map_le`

English:
lemma Ideal.lift_spanRank_map_le
  given: (f : R ->+* T) (I : Ideal R)
  proof: by
  rw [← generators_card I]; rw [lift_spanRank_le_iff_exists_span_set_card_le]
  refine ⟨f '' I.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun s ⟨r, hr, hfr⟩ =>
hfr ▸ mem_map_of_mem _ span_generators I ▸ subset_span hr)) ?_⟩
  refine map_le_of_le_comap (fun r hr => ?_)
  simp only [submodule_span_eq, mem_comap]
  rw [← map_span]; rw [← submodule_span_eq]; rw [span_generators]
  exact mem_map_of_mem f hr

中文:
引理 理想.lift_spanRank_map_le
  条件: (f : R ->+* T) (I : 理想 R)
  证明: by
  rw [← generators_card I]; rw [lift_spanRank_le_iff_exists_span_set_card_le]
  refine ⟨f '' I.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun s ⟨r, hr, hfr⟩ =>
hfr ▸ mem_map_of_mem _ span_generators I ▸ subset_span hr)) ?_⟩
  refine map_le_of_le_comap (fun r hr => ?_)
  simp only [submodule_span_eq, mem_comap]
  rw [← map_span]; rw [← submodule_span_eq]; rw [span_generators]
  exact mem_map_of_mem f hr

Depends on / 依赖: Cardinal, Cardinal.mk_image_le_lift, I.generators, generators, generators_card, le_antisymm, lift_spanRank_le_iff_exists_span_set_card_le, map_le_of_le_comap, map_span, mem_comap, mem_map_of_mem, mk_image_le_lift, span_generators, span_le, submodule_span_eq, subset_span
-/
lemma Ideal.lift_spanRank_map_le (f : R ->+* T) (I : Ideal R) :
    Cardinal.lift.{u} (I.map f).spanRank <= Cardinal.lift.{v} I.spanRank := by
  rw [← generators_card I]; rw [lift_spanRank_le_iff_exists_span_set_card_le]
  refine ⟨f '' I.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun s ⟨r, hr, hfr⟩ =>
hfr ▸ mem_map_of_mem _ span_generators I ▸ subset_span hr)) ?_⟩
  refine map_le_of_le_comap (fun r hr => ?_)
  simp only [submodule_span_eq, mem_comap]
  rw [← map_span]; rw [← submodule_span_eq]; rw [span_generators]
  exact mem_map_of_mem f hr

/--
lemma `Ideal.lift_spanRank_map_eq_of_ringEquiv` / 引理 `Ideal.lift_spanRank_map_eq_of_ringEquiv`

English:
lemma Ideal.lift_spanRank_map_eq_of_ringEquiv
  given: (f : R ≃+* T) (I : Ideal R)
  proof: by
  apply (I.lift_spanRank_map_le (f : R ->+* T)).antisymm
  nth_rw 1 [← Ideal.map_of_equiv f (I := I)]
  exact Ideal.lift_spanRank_map_le (f.symm : T ->+* R) _

中文:
引理 理想.lift_spanRank_map_eq_of_ringEquiv
  条件: (f : R ≃+* T) (I : 理想 R)
  证明: by
  apply (I.lift_spanRank_map_le (f : R ->+* T)).antisymm
  nth_rw 1 [← Ideal.map_of_equiv f (I := I)]
  exact Ideal.lift_spanRank_map_le (f.symm : T ->+* R) _

Depends on / 依赖: I.lift_spanRank_map_le, Ideal.lift_spanRank_map_le, Ideal.map_of_equiv, antisymm, f.symm, lift_spanRank_map_le, map_of_equiv, nth_rw
-/
lemma Ideal.lift_spanRank_map_eq_of_ringEquiv (f : R ≃+* T) (I : Ideal R) :
    Cardinal.lift.{u} (I.map f).spanRank = Cardinal.lift.{v} I.spanRank := by
  apply (I.lift_spanRank_map_le (f : R ->+* T)).antisymm
  nth_rw 1 [← Ideal.map_of_equiv f (I := I)]
  exact Ideal.lift_spanRank_map_le (f.symm : T ->+* R) _

/--
lemma `Ideal.spanRank_map_le` / 引理 `Ideal.spanRank_map_le`

English:
lemma Ideal.spanRank_map_le
  given: (f : R ->+* S) (I : Ideal R)
  statement: (I.map f).spanRank <= I.spanRank
  proof: by
  simpa using I.lift_spanRank_map_le f

@[simp]

中文:
引理 理想.spanRank_map_le
  条件: (f : R ->+* S) (I : 理想 R)
  结论: (I.map f).spanRank <= I.spanRank
  证明: by
  simpa using I.lift_spanRank_map_le f

@[simp]

Depends on / 依赖: I.lift_spanRank_map_le, lift_spanRank_map_le
-/
lemma Ideal.spanRank_map_le (f : R ->+* S) (I : Ideal R) : (I.map f).spanRank <= I.spanRank := by
  simpa using I.lift_spanRank_map_le f

@[simp]
/--
lemma `Ideal.spanRank_map_eq_of_ringEquiv` / 引理 `Ideal.spanRank_map_eq_of_ringEquiv`

English:
lemma Ideal.spanRank_map_eq_of_ringEquiv
  given: (f : R ≃+* S) (I : Ideal R)
  proof: by
  simpa using I.lift_spanRank_map_eq_of_ringEquiv f

中文:
引理 理想.spanRank_map_eq_of_ringEquiv
  条件: (f : R ≃+* S) (I : 理想 R)
  证明: by
  simpa using I.lift_spanRank_map_eq_of_ringEquiv f

Depends on / 依赖: I.lift_spanRank_map_eq_of_ringEquiv, lift_spanRank_map_eq_of_ringEquiv
-/
lemma Ideal.spanRank_map_eq_of_ringEquiv (f : R ≃+* S) (I : Ideal R) :
    (I.map f).spanRank = I.spanRank := by
  simpa using I.lift_spanRank_map_eq_of_ringEquiv f

/--
lemma `Ideal.spanFinrank_map_le_of_fg` / 引理 `Ideal.spanFinrank_map_le_of_fg`

English:
lemma Ideal.spanFinrank_map_le_of_fg
  given: (f : R ->+* T) {I : Ideal R} (hI : I.FG)
  proof: by
  rw [← Submodule.FG.spanRank_le_iff (hI.map f)]; rw [← Cardinal.lift_le.{u}]; rw [Cardinal.lift_natCast]; rw [← Cardinal.lift_natCast.{v}]; rw [← Submodule.FG.spanRank_eq_spanFinrank hI]
  exact I.lift_spanRank_map_le f

@[simp]

中文:
引理 理想.spanFinrank_map_le_of_fg
  条件: (f : R ->+* T) {I : 理想 R} (hI : I.FG)
  证明: by
  rw [← Submodule.FG.spanRank_le_iff (hI.map f)]; rw [← Cardinal.lift_le.{u}]; rw [Cardinal.lift_natCast]; rw [← Cardinal.lift_natCast.{v}]; rw [← Submodule.FG.spanRank_eq_spanFinrank hI]
  exact I.lift_spanRank_map_le f

@[simp]

Depends on / 依赖: Cardinal, Cardinal.lift_le, Cardinal.lift_natCast, I.lift_spanRank_map_le, Submodule, Submodule.FG.spanRank_eq_spanFinrank, Submodule.FG.spanRank_le_iff, hI.map, lift_le, lift_natCast, lift_spanRank_map_le, spanRank_eq_spanFinrank, spanRank_le_iff
-/
lemma Ideal.spanFinrank_map_le_of_fg (f : R ->+* T) {I : Ideal R} (hI : I.FG) :
    (I.map f).spanFinrank <= I.spanFinrank := by
  rw [← Submodule.FG.spanRank_le_iff (hI.map f)]; rw [← Cardinal.lift_le.{u}]; rw [Cardinal.lift_natCast]; rw [← Cardinal.lift_natCast.{v}]; rw [← Submodule.FG.spanRank_eq_spanFinrank hI]
  exact I.lift_spanRank_map_le f

@[simp]
/--
lemma `Ideal.spanFinrank_map_eq_of_ringEquiv` / 引理 `Ideal.spanFinrank_map_eq_of_ringEquiv`

English:
lemma Ideal.spanFinrank_map_eq_of_ringEquiv
  given: (f : R ≃+* T) (I : Ideal R)
  proof: by
  rw [Submodule.spanFinrank]; rw [Submodule.spanFinrank]; rw [← Cardinal.toNat_lift.{u]; rw [v}]; rw [← Cardinal.toNat_lift.{v]; rw [u}]; rw [I.lift_spanRank_map_eq_of_ringEquiv f]

中文:
引理 理想.spanFinrank_map_eq_of_ringEquiv
  条件: (f : R ≃+* T) (I : 理想 R)
  证明: by
  rw [Submodule.spanFinrank]; rw [Submodule.spanFinrank]; rw [← Cardinal.toNat_lift.{u]; rw [v}]; rw [← Cardinal.toNat_lift.{v]; rw [u}]; rw [I.lift_spanRank_map_eq_of_ringEquiv f]

Depends on / 依赖: Cardinal, Cardinal.toNat_lift, I.lift_spanRank_map_eq_of_ringEquiv, Submodule, Submodule.spanFinrank, lift_spanRank_map_eq_of_ringEquiv, spanFinrank, toNat_lift
-/
lemma Ideal.spanFinrank_map_eq_of_ringEquiv (f : R ≃+* T) (I : Ideal R) :
    (I.map f).spanFinrank = I.spanFinrank := by
  rw [Submodule.spanFinrank]; rw [Submodule.spanFinrank]; rw [← Cardinal.toNat_lift.{u]; rw [v}]; rw [← Cardinal.toNat_lift.{v]; rw [u}]; rw [I.lift_spanRank_map_eq_of_ringEquiv f]

end Ideal

end map

section rank

open Cardinal Module Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/--
lemma `Module.Basis.mk_eq_spanRank` / 引理 `Module.Basis.mk_eq_spanRank`

English:
lemma Module.Basis.mk_eq_spanRank
  given: [RankCondition R] {ι : Type*} (v : Basis ι R M)
  proof: by
  rw [← v.span_eq]; rw [spanRank_span_of_linearIndepOn]
  exact v.linearIndependent.linearIndepOn_id

中文:
引理 模.基.mk_eq_spanRank
  条件: [RankCondition R] {ι : 类型} (v : 基 ι R M)
  证明: by
  rw [← v.span_eq]; rw [spanRank_span_of_linearIndepOn]
  exact v.linearIndependent.linearIndepOn_id

Depends on / 依赖: linearIndepOn_id, linearIndependent, spanRank_span_of_linearIndepOn, span_eq, v.linearIndependent.linearIndepOn_id, v.span_eq
-/
lemma Module.Basis.mk_eq_spanRank [RankCondition R] {ι : Type*} (v : Basis ι R M) :
    #(Set.range v) = (⊤ : Submodule R M).spanRank := by
  rw [← v.span_eq]; rw [spanRank_span_of_linearIndepOn]
  exact v.linearIndependent.linearIndepOn_id

/--
theorem `Submodule.rank_eq_spanRank_of_free` / 定理 `Submodule.rank_eq_spanRank_of_free`

English:
theorem Submodule.rank_eq_spanRank_of_free
  given: [Module.Free R M] [StrongRankCondition R]
  proof: by
  have := nontrivial_of_invariantBasisNumber R
  obtain ⟨I, B⟩ := ‹Module.Free R M›
  rw [← Basis.mk_eq_rank'' B]; rw [← Basis.mk_eq_spanRank B]; rw [← Cardinal.lift_id #(Set.range B)]; rw [Cardinal.mk_range_eq_of_injective B.injective]; rw [Cardinal.lift_id _]

中文:
定理 子模.rank_eq_spanRank_of_free
  条件: [模.自由 R M] [StrongRankCondition R]
  证明: by
  have := nontrivial_of_invariantBasisNumber R
  obtain ⟨I, B⟩ := ‹Module.Free R M›
  rw [← Basis.mk_eq_rank'' B]; rw [← Basis.mk_eq_spanRank B]; rw [← Cardinal.lift_id #(Set.range B)]; rw [Cardinal.mk_range_eq_of_injective B.injective]; rw [Cardinal.lift_id _]

Depends on / 依赖: B.injective, Basis.mk_eq_rank, Basis.mk_eq_spanRank, Cardinal, Cardinal.lift_id, Cardinal.mk_range_eq_of_injective, Module, Module.Free, Set.range, injective, lift_id, mk_eq_rank, mk_eq_spanRank, mk_range_eq_of_injective, nontrivial_of_invariantBasisNumber
-/
theorem Submodule.rank_eq_spanRank_of_free [Module.Free R M] [StrongRankCondition R] :
    Module.rank R M = (⊤ : Submodule R M).spanRank := by
  have := nontrivial_of_invariantBasisNumber R
  obtain ⟨I, B⟩ := ‹Module.Free R M›
  rw [← Basis.mk_eq_rank'' B]; rw [← Basis.mk_eq_spanRank B]; rw [← Cardinal.lift_id #(Set.range B)]; rw [Cardinal.mk_range_eq_of_injective B.injective]; rw [Cardinal.lift_id _]

/--
lemma `Module.finrank_eq_spanFinrank_of_free` / 引理 `Module.finrank_eq_spanFinrank_of_free`

English:
lemma Module.finrank_eq_spanFinrank_of_free
  given: [StrongRankCondition R] [Module.Free R M]
  proof: by
  simp [Module.finrank, Submodule.spanFinrank, Submodule.rank_eq_spanRank_of_free]

中文:
引理 模.finrank_eq_spanFinrank_of_free
  条件: [StrongRankCondition R] [模.自由 R M]
  证明: by
  simp [Module.finrank, Submodule.spanFinrank, Submodule.rank_eq_spanRank_of_free]

Depends on / 依赖: Module, Module.finrank, Submodule, Submodule.rank_eq_spanRank_of_free, Submodule.spanFinrank, finrank, rank_eq_spanRank_of_free, spanFinrank
-/
lemma Module.finrank_eq_spanFinrank_of_free [StrongRankCondition R] [Module.Free R M] :
    Module.finrank R M = (⊤ : Submodule R M).spanFinrank := by
  simp [Module.finrank, Submodule.spanFinrank, Submodule.rank_eq_spanRank_of_free]

/--
theorem `Submodule.rank_le_spanRank` / 定理 `Submodule.rank_le_spanRank`

English:
theorem Submodule.rank_le_spanRank
  given: [StrongRankCondition R]
  proof: by
  rw [Module.rank]; rw [Submodule.spanRank]
  refine ciSup_le' (fun ι => (le_ciInf fun s => ?_))
  have := linearIndependent_le_span'' ι.2 s.1 s.2
  simpa

中文:
定理 子模.rank_le_spanRank
  条件: [StrongRankCondition R]
  证明: by
  rw [Module.rank]; rw [Submodule.spanRank]
  refine ciSup_le' (fun ι => (le_ciInf fun s => ?_))
  have := linearIndependent_le_span'' ι.2 s.1 s.2
  simpa

Depends on / 依赖: Module, Module.rank, Submodule, Submodule.spanRank, ciSup_le, le_ciInf, linearIndependent_le_span, spanRank
-/
theorem Submodule.rank_le_spanRank [StrongRankCondition R] :
    Module.rank R M <= (⊤ : Submodule R M).spanRank := by
  rw [Module.rank]; rw [Submodule.spanRank]
  refine ciSup_le' (fun ι => (le_ciInf fun s => ?_))
  have := linearIndependent_le_span'' ι.2 s.1 s.2
  simpa

end rank
