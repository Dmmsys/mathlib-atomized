/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of subsets: monotonicity, closure, union

This file contains general results about the topological entropy of various subsets of the same
dynamical system `(X, T)`. We prove that:
- the topological entropy `CoverEntropy T F` of `F` is monotone in `F`: the larger the subset,
  the larger its entropy.
- the topological entropy of a subset equals the entropy of its closure.
- the entropy of the union of two sets is the maximum of their entropies. We generalize
  the latter property to finite unions.

## Implementation notes

Most results are proved using only the definition of the topological entropy by covers. Some lemmas
of general interest are also proved for nets.

## TODO

One may implement a notion of Hausdorff convergence for subsets using uniform
spaces, and then prove the semicontinuity of the topological entropy. It would be a nice
generalization of the lemmas on closures.

## Tags

closure, entropy, subset, union
-/

@[expose] public section

namespace Dynamics

open ExpGrowth Set UniformSpace
open scoped SetRel Uniformity

variable {X : Type*} {T : X -> X} {F G s t : Set X} {U V : SetRel X X} {n : Nat}

/-! ### Monotonicity of entropy as a function of the subset -/

section Subset

/--
lemma `IsDynCoverOf.monotone_subset` / 引理 `IsDynCoverOf.monotone_subset`

English:
lemma IsDynCoverOf.monotone_subset
  given: (F_G : F subseteq G) (h : IsDynCoverOf T G U n s)
  proof: F_G.trans h

中文:
引理 IsDynCoverOf.monotone_subset
  条件: (F_G : F subseteq G) (h : IsDynCoverOf T G U n s)
  证明: F_G.trans h

Depends on / 依赖: F_G.trans
-/
lemma IsDynCoverOf.monotone_subset (F_G : F subseteq G) (h : IsDynCoverOf T G U n s) :
    IsDynCoverOf T F U n s :=
  F_G.trans h

/--
lemma `IsDynNetIn.monotone_subset` / 引理 `IsDynNetIn.monotone_subset`

English:
lemma IsDynNetIn.monotone_subset
  given: (F_G : F subseteq G) (h : IsDynNetIn T F U n s)
  statement: IsDynNetIn T G U n s
  proof: ⟨h.1.trans F_G, h.2⟩

中文:
引理 IsDynNetIn.monotone_subset
  条件: (F_G : F subseteq G) (h : IsDynNetIn T F U n s)
  结论: IsDynNetIn T G U n s
  证明: ⟨h.1.trans F_G, h.2⟩
-/
lemma IsDynNetIn.monotone_subset (F_G : F subseteq G) (h : IsDynNetIn T F U n s) : IsDynNetIn T G U n s :=
  ⟨h.1.trans F_G, h.2⟩

/--
lemma `coverMincard_monotone_subset` / 引理 `coverMincard_monotone_subset`

English:
lemma coverMincard_monotone_subset
  given: (T : X -> X) (U : SetRel X X) (n : Nat)
  proof: fun _ _ F_G => biInf_mono fun _ h => h.monotone_subset F_G

中文:
引理 coverMincard_monotone_subset
  条件: (T : X -> X) (U : SetRel X X) (n : 自然数)
  证明: fun _ _ F_G => biInf_mono fun _ h => h.monotone_subset F_G

Depends on / 依赖: biInf_mono, h.monotone_subset, monotone_subset
-/
lemma coverMincard_monotone_subset (T : X -> X) (U : SetRel X X) (n : Nat) :
    Monotone fun F : Set X => coverMincard T F U n :=
  fun _ _ F_G => biInf_mono fun _ h => h.monotone_subset F_G

/--
lemma `netMaxcard_monotone_subset` / 引理 `netMaxcard_monotone_subset`

English:
lemma netMaxcard_monotone_subset
  given: (T : X -> X) (U : SetRel X X) (n : Nat)
  proof: fun _ _ F_G => biSup_mono fun _ h => h.monotone_subset F_G

中文:
引理 netMaxcard_monotone_subset
  条件: (T : X -> X) (U : SetRel X X) (n : 自然数)
  证明: fun _ _ F_G => biSup_mono fun _ h => h.monotone_subset F_G

Depends on / 依赖: biSup_mono, h.monotone_subset, monotone_subset
-/
lemma netMaxcard_monotone_subset (T : X -> X) (U : SetRel X X) (n : Nat) :
    Monotone fun F : Set X => netMaxcard T F U n :=
  fun _ _ F_G => biSup_mono fun _ h => h.monotone_subset F_G

/--
lemma `coverEntropyInfEntourage_monotone` / 引理 `coverEntropyInfEntourage_monotone`

English:
lemma coverEntropyInfEntourage_monotone
  given: (T : X -> X) (U : SetRel X X)
  proof: by
  refine fun F G F_G => ExpGrowth.expGrowthInf_monotone fun n => ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

中文:
引理 coverEntropyInfEntourage_monotone
  条件: (T : X -> X) (U : SetRel X X)
  证明: by
  refine fun F G F_G => ExpGrowth.expGrowthInf_monotone fun n => ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

Depends on / 依赖: ENat.toENNReal_mono, ExpGrowth, ExpGrowth.expGrowthInf_monotone, coverMincard_monotone_subset, expGrowthInf_monotone, toENNReal_mono
-/
lemma coverEntropyInfEntourage_monotone (T : X -> X) (U : SetRel X X) :
    Monotone fun F : Set X => coverEntropyInfEntourage T F U := by
  refine fun F G F_G => ExpGrowth.expGrowthInf_monotone fun n => ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

/--
lemma `coverEntropyEntourage_monotone` / 引理 `coverEntropyEntourage_monotone`

English:
lemma coverEntropyEntourage_monotone
  given: (T : X -> X) (U : SetRel X X)
  proof: by
  refine fun F G F_G => ExpGrowth.expGrowthSup_monotone fun n => ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

中文:
引理 coverEntropyEntourage_monotone
  条件: (T : X -> X) (U : SetRel X X)
  证明: by
  refine fun F G F_G => ExpGrowth.expGrowthSup_monotone fun n => ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

Depends on / 依赖: ENat.toENNReal_mono, ExpGrowth, ExpGrowth.expGrowthSup_monotone, coverMincard_monotone_subset, expGrowthSup_monotone, toENNReal_mono
-/
lemma coverEntropyEntourage_monotone (T : X -> X) (U : SetRel X X) :
    Monotone fun F : Set X => coverEntropyEntourage T F U := by
  refine fun F G F_G => ExpGrowth.expGrowthSup_monotone fun n => ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

/--
lemma `netEntropyInfEntourage_monotone` / 引理 `netEntropyInfEntourage_monotone`

English:
lemma netEntropyInfEntourage_monotone
  given: (T : X -> X) (U : SetRel X X)
  proof: by
  refine fun F G F_G => ExpGrowth.expGrowthInf_monotone fun n => ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

中文:
引理 netEntropyInfEntourage_monotone
  条件: (T : X -> X) (U : SetRel X X)
  证明: by
  refine fun F G F_G => ExpGrowth.expGrowthInf_monotone fun n => ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

Depends on / 依赖: ENat.toENNReal_mono, ExpGrowth, ExpGrowth.expGrowthInf_monotone, expGrowthInf_monotone, netMaxcard_monotone_subset, toENNReal_mono
-/
lemma netEntropyInfEntourage_monotone (T : X -> X) (U : SetRel X X) :
    Monotone fun F : Set X => netEntropyInfEntourage T F U := by
  refine fun F G F_G => ExpGrowth.expGrowthInf_monotone fun n => ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

/--
lemma `netEntropyEntourage_monotone` / 引理 `netEntropyEntourage_monotone`

English:
lemma netEntropyEntourage_monotone
  given: (T : X -> X) (U : SetRel X X)
  proof: by
  refine fun F G F_G => ExpGrowth.expGrowthSup_monotone fun n => ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

中文:
引理 netEntropyEntourage_monotone
  条件: (T : X -> X) (U : SetRel X X)
  证明: by
  refine fun F G F_G => ExpGrowth.expGrowthSup_monotone fun n => ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

Depends on / 依赖: ENat.toENNReal_mono, ExpGrowth, ExpGrowth.expGrowthSup_monotone, expGrowthSup_monotone, netMaxcard_monotone_subset, toENNReal_mono
-/
lemma netEntropyEntourage_monotone (T : X -> X) (U : SetRel X X) :
    Monotone fun F : Set X => netEntropyEntourage T F U := by
  refine fun F G F_G => ExpGrowth.expGrowthSup_monotone fun n => ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

/--
lemma `coverEntropyInf_monotone` / 引理 `coverEntropyInf_monotone`

English:
lemma coverEntropyInf_monotone
  given: [UniformSpace X] (T : X -> X)
  proof: fun _ _ F_G => iSup₂_mono fun U _ => coverEntropyInfEntourage_monotone T U F_G

中文:
引理 coverEntropyInf_monotone
  条件: [一致空间 X] (T : X -> X)
  证明: fun _ _ F_G => iSup₂_mono fun U _ => coverEntropyInfEntourage_monotone T U F_G

Depends on / 依赖: coverEntropyInfEntourage_monotone
-/
lemma coverEntropyInf_monotone [UniformSpace X] (T : X -> X) :
    Monotone fun F : Set X => coverEntropyInf T F :=
  fun _ _ F_G => iSup₂_mono fun U _ => coverEntropyInfEntourage_monotone T U F_G

/--
lemma `coverEntropy_monotone` / 引理 `coverEntropy_monotone`

English:
lemma coverEntropy_monotone
  given: [UniformSpace X] (T : X -> X)
  proof: fun _ _ F_G => iSup₂_mono fun U _ => coverEntropyEntourage_monotone T U F_G

中文:
引理 coverEntropy_monotone
  条件: [一致空间 X] (T : X -> X)
  证明: fun _ _ F_G => iSup₂_mono fun U _ => coverEntropyEntourage_monotone T U F_G

Depends on / 依赖: coverEntropyEntourage_monotone
-/
lemma coverEntropy_monotone [UniformSpace X] (T : X -> X) :
    Monotone fun F : Set X => coverEntropy T F :=
  fun _ _ F_G => iSup₂_mono fun U _ => coverEntropyEntourage_monotone T U F_G

end Subset

/-! ### Closure -/

section Closure

variable [UniformSpace X]

/--
lemma `IsDynCoverOf.closure` / 引理 `IsDynCoverOf.closure`

English:
lemma IsDynCoverOf.closure
  statement: (h : Continuous T)
  proof: by
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_V⟩
  refine IsDynCoverOf.of_entourage_subset (SetRel.comp_subset_comp_left W_V) fun x hx => ?_
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_nhds.1 hx _ (ball_dynEntourage_mem_nhds h W_uni n x)
  obtain ⟨z, hz, hyz⟩ := s_cover hy
  exact ⟨z, hz, dynEntourage_comp_subset _ _ _ _ ⟨y, hxy, hyz⟩⟩

中文:
引理 IsDynCoverOf.closure
  结论: (h : 连续 T)
  证明: by
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_V⟩
  refine IsDynCoverOf.of_entourage_subset (SetRel.comp_subset_comp_left W_V) fun x hx => ?_
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_nhds.1 hx _ (ball_dynEntourage_mem_nhds h W_uni n x)
  obtain ⟨z, hz, hyz⟩ := s_cover hy
  exact ⟨z, hz, dynEntourage_comp_subset _ _ _ _ ⟨y, hxy, hyz⟩⟩

Depends on / 依赖: IsDynCoverOf, IsDynCoverOf.of_entourage_subset, SetRel, SetRel.comp_subset_comp_left, V_uni, W_symm, W_uni, ball_dynEntourage_mem_nhds, comp_subset_comp_left, dynEntourage_comp_subset, hasBasis_symmetric, hasBasis_symmetric.mem_iff, mem_closure_iff_nhds, mem_iff, of_entourage_subset, s_cover
-/
lemma IsDynCoverOf.closure (h : Continuous T)
    (V_uni : V in 𝓤 X) (s_cover : IsDynCoverOf T F U n s) :
    IsDynCoverOf T (closure F) (V ○ U) n s := by
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_V⟩
  refine IsDynCoverOf.of_entourage_subset (SetRel.comp_subset_comp_left W_V) fun x hx => ?_
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_nhds.1 hx _ (ball_dynEntourage_mem_nhds h W_uni n x)
  obtain ⟨z, hz, hyz⟩ := s_cover hy
  exact ⟨z, hz, dynEntourage_comp_subset _ _ _ _ ⟨y, hxy, hyz⟩⟩

/--
lemma `coverMincard_closure_le` / 引理 `coverMincard_closure_le`

English:
lemma coverMincard_closure_le
  statement: (h : Continuous T) (F : Set X) (U : SetRel X X)
  proof: by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 h'
  exact s_coverMincard ▸ (s_cover.closure h V_uni).coverMincard_le_card

中文:
引理 coverMincard_closure_le
  结论: (h : 连续 T) (F : 集合 X) (U : SetRel X X)
  证明: by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 h'
  exact s_coverMincard ▸ (s_cover.closure h V_uni).coverMincard_le_card

Depends on / 依赖: V_uni, closure, coverMincard, coverMincard_finite_iff, coverMincard_le_card, eq_top_or_lt_top, le_top, s_cover, s_cover.closure, s_coverMincard
-/
lemma coverMincard_closure_le (h : Continuous T) (F : Set X) (U : SetRel X X)
    (V_uni : V in 𝓤 X) (n : Nat) :
    coverMincard T (closure F) (V ○ U) n <= coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 h'
  exact s_coverMincard ▸ (s_cover.closure h V_uni).coverMincard_le_card

/--
lemma `coverEntropyInfEntourage_closure` / 引理 `coverEntropyInfEntourage_closure`

English:
lemma coverEntropyInfEntourage_closure
  statement: (h : Continuous T) (F : Set X) (U : SetRel X X)
  proof: expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)

中文:
引理 coverEntropyInfEntourage_closure
  结论: (h : 连续 T) (F : 集合 X) (U : SetRel X X)
  证明: expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)

Depends on / 依赖: ENat.toENNReal_mono, V_uni, coverMincard_closure_le, expGrowthInf_monotone, toENNReal_mono
-/
lemma coverEntropyInfEntourage_closure (h : Continuous T) (F : Set X) (U : SetRel X X)
    (V_uni : V in 𝓤 X) :
    coverEntropyInfEntourage T (closure F) (V ○ U) <= coverEntropyInfEntourage T F U :=
  expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)

/--
lemma `coverEntropyEntourage_closure` / 引理 `coverEntropyEntourage_closure`

English:
lemma coverEntropyEntourage_closure
  statement: (h : Continuous T) (F : Set X) (U : SetRel X X)
  proof: expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)

中文:
引理 coverEntropyEntourage_closure
  结论: (h : 连续 T) (F : 集合 X) (U : SetRel X X)
  证明: expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)

Depends on / 依赖: ENat.toENNReal_mono, V_uni, coverMincard_closure_le, expGrowthSup_monotone, toENNReal_mono
-/
lemma coverEntropyEntourage_closure (h : Continuous T) (F : Set X) (U : SetRel X X)
    (V_uni : V in 𝓤 X) :
    coverEntropyEntourage T (closure F) (V ○ U) <= coverEntropyEntourage T F U :=
  expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)

/--
lemma `coverEntropyInf_closure` / 引理 `coverEntropyInf_closure`

English:
lemma coverEntropyInf_closure
  given: (h : Continuous T)
  proof: by
  refine (iSup₂_le fun U U_uni => ?_).antisymm (coverEntropyInf_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyInfEntourage_antitone T (closure F) V_U).trans
    (coverEntropyInfEntourage_closure h F V V_uni))

中文:
引理 coverEntropyInf_closure
  条件: (h : 连续 T)
  证明: by
  refine (iSup₂_le fun U U_uni => ?_).antisymm (coverEntropyInf_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyInfEntourage_antitone T (closure F) V_U).trans
    (coverEntropyInfEntourage_closure h F V V_uni))

Depends on / 依赖: U_uni, V_uni, antisymm, closure, comp_mem_uniformity_sets, coverEntropyInfEntourage_antitone, coverEntropyInfEntourage_closure, coverEntropyInf_monotone, subset_closure
-/
lemma coverEntropyInf_closure (h : Continuous T) :
    coverEntropyInf T (closure F) = coverEntropyInf T F := by
  refine (iSup₂_le fun U U_uni => ?_).antisymm (coverEntropyInf_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyInfEntourage_antitone T (closure F) V_U).trans
    (coverEntropyInfEntourage_closure h F V V_uni))

/--
theorem `coverEntropy_closure` / 定理 `coverEntropy_closure`

English:
theorem coverEntropy_closure
  given: (h : Continuous T)
  proof: by
  refine (iSup₂_le fun U U_uni => ?_).antisymm (coverEntropy_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyEntourage_antitone T (closure F) V_U).trans
    (coverEntropyEntourage_closure h F V V_uni))

中文:
定理 coverEntropy_closure
  条件: (h : 连续 T)
  证明: by
  refine (iSup₂_le fun U U_uni => ?_).antisymm (coverEntropy_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyEntourage_antitone T (closure F) V_U).trans
    (coverEntropyEntourage_closure h F V V_uni))

Depends on / 依赖: U_uni, V_uni, antisymm, closure, comp_mem_uniformity_sets, coverEntropyEntourage_antitone, coverEntropyEntourage_closure, coverEntropy_monotone, subset_closure
-/
theorem coverEntropy_closure (h : Continuous T) :
    coverEntropy T (closure F) = coverEntropy T F := by
  refine (iSup₂_le fun U U_uni => ?_).antisymm (coverEntropy_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyEntourage_antitone T (closure F) V_U).trans
    (coverEntropyEntourage_closure h F V V_uni))

end Closure

/-! ### Finite unions -/

section Union

/--
lemma `IsDynCoverOf.union` / 引理 `IsDynCoverOf.union`

English:
lemma IsDynCoverOf.union
  given: (hs : IsDynCoverOf T F U n s) (ht : IsDynCoverOf T G U n t)
  proof: SetRel.IsCover.union hs ht

中文:
引理 IsDynCoverOf.union
  条件: (hs : IsDynCoverOf T F U n s) (ht : IsDynCoverOf T G U n t)
  证明: SetRel.IsCover.union hs ht

Depends on / 依赖: IsCover, SetRel, SetRel.IsCover.union
-/
lemma IsDynCoverOf.union (hs : IsDynCoverOf T F U n s) (ht : IsDynCoverOf T G U n t) :
    IsDynCoverOf T (F union G) U n (s union t) := SetRel.IsCover.union hs ht

/--
lemma `coverMincard_union_le` / 引理 `coverMincard_union_le`

English:
lemma coverMincard_union_le
  given: (T : X -> X) (F G : Set X) (U : SetRel X X) (n : Nat)
  proof: by
  classical
  rcases eq_top_or_lt_top (coverMincard T F U n) with hF | hF
  · rw [hF, top_add]; exact le_top
  rcases eq_top_or_lt_top (coverMincard T G U n) with hG | hG
  · rw [hG, add_top]; exact le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 hF
  obtain ⟨t, t_cover, t_coverMincard⟩ := (coverMincard_finite_iff T G U n).1 hG
  rw [← s_coverMincard]; rw [← t_coverMincard]; rw [← ENat.natCast_add]
  apply (IsDynCoverOf.coverMincard_le_card _).trans (WithTop.coe_mono (s.card_union_le t))
  rw [s.coe_union t]
  exact s_cover.union t_cover

中文:
引理 coverMincard_union_le
  条件: (T : X -> X) (F G : 集合 X) (U : SetRel X X) (n : 自然数)
  证明: by
  classical
  rcases eq_top_or_lt_top (coverMincard T F U n) with hF | hF
  · rw [hF, top_add]; exact le_top
  rcases eq_top_or_lt_top (coverMincard T G U n) with hG | hG
  · rw [hG, add_top]; exact le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 hF
  obtain ⟨t, t_cover, t_coverMincard⟩ := (coverMincard_finite_iff T G U n).1 hG
  rw [← s_coverMincard]; rw [← t_coverMincard]; rw [← ENat.natCast_add]
  apply (IsDynCoverOf.coverMincard_le_card _).trans (WithTop.coe_mono (s.card_union_le t))
  rw [s.coe_union t]
  exact s_cover.union t_cover

Depends on / 依赖: ENat.natCast_add, IsDynCoverOf, IsDynCoverOf.coverMincard_le_card, WithTop, WithTop.coe_mono, add_top, classical, coe_mono, coverMincard, coverMincard_finite_iff, coverMincard_le_card, eq_top_or_lt_top, le_top, natCast_add, s.card, s_cover, s_coverMincard, t_cover, t_coverMincard, top_add
-/
lemma coverMincard_union_le (T : X -> X) (F G : Set X) (U : SetRel X X) (n : Nat) :
    coverMincard T (F union G) U n <= coverMincard T F U n + coverMincard T G U n := by
  classical
  rcases eq_top_or_lt_top (coverMincard T F U n) with hF | hF
  · rw [hF, top_add]; exact le_top
  rcases eq_top_or_lt_top (coverMincard T G U n) with hG | hG
  · rw [hG, add_top]; exact le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 hF
  obtain ⟨t, t_cover, t_coverMincard⟩ := (coverMincard_finite_iff T G U n).1 hG
  rw [← s_coverMincard]; rw [← t_coverMincard]; rw [← ENat.natCast_add]
  apply (IsDynCoverOf.coverMincard_le_card _).trans (WithTop.coe_mono (s.card_union_le t))
  rw [s.coe_union t]
  exact s_cover.union t_cover

/--
lemma `coverEntropyEntourage_union` / 引理 `coverEntropyEntourage_union`

English:
lemma coverEntropyEntourage_union
  proof: by
  refine le_antisymm ?_ ?_
  · apply le_of_le_of_eq (expGrowthSup_monotone fun n => ?_) expGrowthSup_add
    rw [Pi.add_apply]; rw [← ENat.toENNReal_add]
    exact ENat.toENNReal_mono (coverMincard_union_le T F G U n)
  · exact max_le (coverEntropyEntourage_monotone T U subset_union_left)
      (coverEntropyEntourage_monotone T U subset_union_right)

中文:
引理 coverEntropyEntourage_union
  证明: by
  refine le_antisymm ?_ ?_
  · apply le_of_le_of_eq (expGrowthSup_monotone fun n => ?_) expGrowthSup_add
    rw [Pi.add_apply]; rw [← ENat.toENNReal_add]
    exact ENat.toENNReal_mono (coverMincard_union_le T F G U n)
  · exact max_le (coverEntropyEntourage_monotone T U subset_union_left)
      (coverEntropyEntourage_monotone T U subset_union_right)

Depends on / 依赖: ENat.toENNReal_add, ENat.toENNReal_mono, Pi.add_apply, add_apply, coverEntropyEntourage_monotone, coverMincard_union_le, expGrowthSup_add, expGrowthSup_monotone, le_antisymm, le_of_le_of_eq, max_le, subset_union_left, subset_union_right, toENNReal_add, toENNReal_mono
-/
lemma coverEntropyEntourage_union :
    coverEntropyEntourage T (F union G) U
      = max (coverEntropyEntourage T F U) (coverEntropyEntourage T G U) := by
  refine le_antisymm ?_ ?_
  · apply le_of_le_of_eq (expGrowthSup_monotone fun n => ?_) expGrowthSup_add
    rw [Pi.add_apply]; rw [← ENat.toENNReal_add]
    exact ENat.toENNReal_mono (coverMincard_union_le T F G U n)
  · exact max_le (coverEntropyEntourage_monotone T U subset_union_left)
      (coverEntropyEntourage_monotone T U subset_union_right)

variable {ι : Type*} [UniformSpace X]

/--
lemma `coverEntropy_union` / 引理 `coverEntropy_union`

English:
lemma coverEntropy_union
  proof: by
  simp only [coverEntropy, ← iSup_sup_eq]
  exact biSup_congr fun _ _ => coverEntropyEntourage_union

中文:
引理 coverEntropy_union
  证明: by
  simp only [coverEntropy, ← iSup_sup_eq]
  exact biSup_congr fun _ _ => coverEntropyEntourage_union

Depends on / 依赖: biSup_congr, coverEntropy, coverEntropyEntourage_union, iSup_sup_eq
-/
lemma coverEntropy_union :
    coverEntropy T (F union G) = max (coverEntropy T F) (coverEntropy T G) := by
  simp only [coverEntropy, ← iSup_sup_eq]
  exact biSup_congr fun _ _ => coverEntropyEntourage_union

/--
lemma `coverEntropyInf_iUnion_le` / 引理 `coverEntropyInf_iUnion_le`

English:
lemma coverEntropyInf_iUnion_le
  given: (T : X -> X) (F : ι -> Set X)
  proof: iSup_le fun i => coverEntropyInf_monotone T (subset_iUnion F i)

中文:
引理 coverEntropyInf_iUnion_le
  条件: (T : X -> X) (F : ι -> 集合 X)
  证明: iSup_le fun i => coverEntropyInf_monotone T (subset_iUnion F i)

Depends on / 依赖: coverEntropyInf_monotone, iSup_le, subset_iUnion
-/
lemma coverEntropyInf_iUnion_le (T : X -> X) (F : ι -> Set X) :
    ⨆ i, coverEntropyInf T (F i) <= coverEntropyInf T (⋃ i, F i) :=
  iSup_le fun i => coverEntropyInf_monotone T (subset_iUnion F i)

/--
lemma `coverEntropy_iUnion_le` / 引理 `coverEntropy_iUnion_le`

English:
lemma coverEntropy_iUnion_le
  given: (T : X -> X) (F : ι -> Set X)
  proof: iSup_le fun i => coverEntropy_monotone T (subset_iUnion F i)

中文:
引理 coverEntropy_iUnion_le
  条件: (T : X -> X) (F : ι -> 集合 X)
  证明: iSup_le fun i => coverEntropy_monotone T (subset_iUnion F i)

Depends on / 依赖: coverEntropy_monotone, iSup_le, subset_iUnion
-/
lemma coverEntropy_iUnion_le (T : X -> X) (F : ι -> Set X) :
    ⨆ i, coverEntropy T (F i) <= coverEntropy T (⋃ i, F i) :=
  iSup_le fun i => coverEntropy_monotone T (subset_iUnion F i)

/--
lemma `coverEntropyInf_biUnion_le` / 引理 `coverEntropyInf_biUnion_le`

English:
lemma coverEntropyInf_biUnion_le
  given: (s : Set ι) (T : X -> X) (F : ι -> Set X)
  proof: iSup₂_le fun _ i_s => coverEntropyInf_monotone T (subset_biUnion_of_mem i_s)

中文:
引理 coverEntropyInf_biUnion_le
  条件: (s : 集合 ι) (T : X -> X) (F : ι -> 集合 X)
  证明: iSup₂_le fun _ i_s => coverEntropyInf_monotone T (subset_biUnion_of_mem i_s)

Depends on / 依赖: coverEntropyInf_monotone, subset_biUnion_of_mem
-/
lemma coverEntropyInf_biUnion_le (s : Set ι) (T : X -> X) (F : ι -> Set X) :
    ⨆ i in s, coverEntropyInf T (F i) <= coverEntropyInf T (⋃ i in s, F i) :=
  iSup₂_le fun _ i_s => coverEntropyInf_monotone T (subset_biUnion_of_mem i_s)

/--
lemma `coverEntropy_biUnion_le` / 引理 `coverEntropy_biUnion_le`

English:
lemma coverEntropy_biUnion_le
  given: (s : Set ι) (T : X -> X) (F : ι -> Set X)
  proof: iSup₂_le fun _ i_s => coverEntropy_monotone T (subset_biUnion_of_mem i_s)

中文:
引理 coverEntropy_biUnion_le
  条件: (s : 集合 ι) (T : X -> X) (F : ι -> 集合 X)
  证明: iSup₂_le fun _ i_s => coverEntropy_monotone T (subset_biUnion_of_mem i_s)

Depends on / 依赖: coverEntropy_monotone, subset_biUnion_of_mem
-/
lemma coverEntropy_biUnion_le (s : Set ι) (T : X -> X) (F : ι -> Set X) :
    ⨆ i in s, coverEntropy T (F i) <= coverEntropy T (⋃ i in s, F i) :=
  iSup₂_le fun _ i_s => coverEntropy_monotone T (subset_biUnion_of_mem i_s)

/--
Definition of `coverEntropySupBotHom` / `coverEntropySupBotHom` 的定义

English:
definition coverEntropySupBotHom
  signature: (T : X -> X)
  body: coverEntropy T
  map_sup' := fun _ _ => coverEntropy_union
  map_bot' := coverEntropy_empty

@[deprecated (since := "2026-07-25")]
alias coverEntropy_supBotHom := coverEntropySupBotHom

中文:
定义 coverEntropySupBotHom
  签名: (T : X -> X)
  定义体: coverEntropy T
  map_sup' := fun _ _ => coverEntropy_union
  map_bot' := coverEntropy_empty

@[deprecated (since := "2026-07-25")]
alias coverEntropy_supBotHom := coverEntropySupBotHom

Depends on / 依赖: coverEntropy
-/
noncomputable def coverEntropySupBotHom (T : X -> X) :
    SupBotHom (Set X) EReal where
  toFun := coverEntropy T
  map_sup' := fun _ _ => coverEntropy_union
  map_bot' := coverEntropy_empty

@[deprecated (since := "2026-07-25")]
alias coverEntropy_supBotHom := coverEntropySupBotHom

/--
lemma `coverEntropy_iUnion_of_finite` / 引理 `coverEntropy_iUnion_of_finite`

English:
lemma coverEntropy_iUnion_of_finite
  given: [Finite ι] {T : X -> X} {F : ι -> Set X}
  proof: map_finite_iSup (coverEntropySupBotHom T) F

中文:
引理 coverEntropy_iUnion_of_finite
  条件: [有限 ι] {T : X -> X} {F : ι -> 集合 X}
  证明: map_finite_iSup (coverEntropySupBotHom T) F

Depends on / 依赖: coverEntropySupBotHom, map_finite_iSup
-/
lemma coverEntropy_iUnion_of_finite [Finite ι] {T : X -> X} {F : ι -> Set X} :
    coverEntropy T (⋃ i : ι, F i) = ⨆ i : ι, coverEntropy T (F i) :=
  map_finite_iSup (coverEntropySupBotHom T) F

/--
lemma `coverEntropy_biUnion_finset` / 引理 `coverEntropy_biUnion_finset`

English:
lemma coverEntropy_biUnion_finset
  given: {T : X -> X} {F : ι -> Set X} {s : Finset ι}
  proof: by
  have := map_finset_sup (coverEntropySupBotHom T) s F
  rw [s.sup_set_eq_biUnion]; rw [s.sup_eq_iSup]; rw [coverEntropySupBotHom]; rw [SupBotHom.coe_mk]; rw [SupHom.coe_mk] at this
  rw [this]
  congr

中文:
引理 coverEntropy_biUnion_finset
  条件: {T : X -> X} {F : ι -> 集合 X} {s : 有限集 ι}
  证明: by
  have := map_finset_sup (coverEntropySupBotHom T) s F
  rw [s.sup_set_eq_biUnion]; rw [s.sup_eq_iSup]; rw [coverEntropySupBotHom]; rw [SupBotHom.coe_mk]; rw [SupHom.coe_mk] at this
  rw [this]
  congr

Depends on / 依赖: SupBotHom, SupBotHom.coe_mk, SupHom, SupHom.coe_mk, coe_mk, coverEntropySupBotHom, map_finset_sup, s.sup_eq_iSup, s.sup_set_eq_biUnion, sup_eq_iSup, sup_set_eq_biUnion
-/
lemma coverEntropy_biUnion_finset {T : X -> X} {F : ι -> Set X} {s : Finset ι} :
    coverEntropy T (⋃ i in s, F i) = ⨆ i in s, coverEntropy T (F i) := by
  have := map_finset_sup (coverEntropySupBotHom T) s F
  rw [s.sup_set_eq_biUnion]; rw [s.sup_eq_iSup]; rw [coverEntropySupBotHom]; rw [SupBotHom.coe_mk]; rw [SupHom.coe_mk] at this
  rw [this]
  congr

end Union

end Dynamics
