/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Nakayama's lemma

This file contains some alternative statements of Nakayama's Lemma as found in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

## Main statements

* `Submodule.eq_smul_of_le_smul_of_le_jacobson` - A version of (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV),
  generalising to the Jacobson of any ideal.
* `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` - Statement (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

* `Submodule.sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` - A version of (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV),
  generalising to the Jacobson of any ideal.
* `Submodule.smul_le_of_le_smul_of_le_jacobson_bot` - Statement (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

* `Submodule.exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot` -
  Statement (8) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

Note that a version of Statement (1) in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV) can be found in
`RingTheory.Finiteness` under the name
`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`

## References
* [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV)

## Tags
Nakayama, Jacobson
-/

public section


variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open Ideal

namespace Submodule

/-- **Nakayama's Lemma** - A slightly more general version of (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_bot_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`. -/
@[stacks 00DV "(2)"]
/--
theorem `eq_smul_of_le_smul_of_le_jacobson` / 定理 `eq_smul_of_le_smul_of_le_jacobson`

English:
theorem eq_smul_of_le_smul_of_le_jacobson
  statement: {I J : Ideal R} {N : Submodule R M} (hN : N.FG)
  proof: by
  refine le_antisymm ?_ (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _)
  intro n hn
  obtain ⟨r, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN
  obtain ⟨s, hs⟩ := exists_mul_sub_mem_of_sub_one_mem_jacobson r (hIjac hr.1)
  have : n = -(s * r - 1) • n 

中文:
定理 eq_smul_of_le_smul_of_le_jacobson
  结论: {I J : Ideal R} {N : Submodule R M} (hN : N.FG)
  证明: by
  refine le_antisymm ?_ (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _)
  intro n hn
  obtain ⟨r, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN
  obtain ⟨s, hs⟩ := exists_mul_sub_mem_of_sub_one_mem_jacobson r (hIjac hr.1)
  have : n = -(s * r - 1) • n 

Depends on / 依赖: Submodule, Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul, Submodule.neg_mem, Submodule.smul_le, Submodule.smul_mem, Submodule.smul_mem_smul, exists_mul_sub_mem_of_sub_one_mem_jacobson, exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul, le_antisymm, mul_smul, neg_mem, neg_sub, one_smul, smul_le, smul_mem, smul_mem_smul, smul_zero, sub_smul, sub_zero
-/
theorem eq_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N : Submodule R M} (hN : N.FG)
    (hIN : N <= I • N) (hIjac : I <= jacobson J) : N = J • N := by
  refine le_antisymm ?_ (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _)
  intro n hn
  obtain ⟨r, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN
  obtain ⟨s, hs⟩ := exists_mul_sub_mem_of_sub_one_mem_jacobson r (hIjac hr.1)
  have : n = -(s * r - 1) • n := by
    rw [neg_sub]; rw [sub_smul]; rw [mul_smul]; rw [hr.2 n hn]; rw [one_smul]; rw [smul_zero]; rw [sub_zero]
  rw [this]
  exact Submodule.smul_mem_smul (Submodule.neg_mem _ hs) hn

/--
lemma `eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator` / 引理 `eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator`

English:
lemma eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator
  statement: {I : Ideal R}
  proof: (eq_smul_of_le_smul_of_le_jacobson hN hIN.le hIjac).trans N.annihilator_smul

中文:
引理 eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator
  结论: {I : Ideal R}
  证明: (eq_smul_of_le_smul_of_le_jacobson hN hIN.le hIjac).trans N.annihilator_smul

Depends on / 依赖: N.annihilator_smul, annihilator_smul, eq_smul_of_le_smul_of_le_jacobson, hIN.le
-/
lemma eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator {I : Ideal R}
    {N : Submodule R M} (hN : FG N) (hIN : N = I • N)
    (hIjac : I <= N.annihilator.jacobson) : N = ⊥ :=
  (eq_smul_of_le_smul_of_le_jacobson hN hIN.le hIjac).trans N.annihilator_smul

open scoped Pointwise in
/--
lemma `eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator` / 引理 `eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator`

English:
lemma eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator
  statement: {r : R}
  proof: eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hrN (ideal_span_singleton_smul r N).symm)
    ((span_singleton_le_iff_mem r _).mpr hrJac)

中文:
引理 eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator
  结论: {r : R}
  证明: eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hrN (ideal_span_singleton_smul r N).symm)
    ((span_singleton_le_iff_mem r _).mpr hrJac)

Depends on / 依赖: Eq.trans, eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator, ideal_span_singleton_smul, span_singleton_le_iff_mem
-/
lemma eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator {r : R}
    {N : Submodule R M} (hN : FG N) (hrN : N = r • N)
    (hrJac : r in N.annihilator.jacobson) : N = ⊥ :=
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hrN (ideal_span_singleton_smul r N).symm)
    ((span_singleton_le_iff_mem r _).mpr hrJac)

open scoped Pointwise in
/--
lemma `eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator` / 引理 `eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator`

English:
lemma eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator
  statement: {s : Set R}
  proof: eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hsN (span_smul_eq s N).symm) (span_le.mpr hsJac)

中文:
引理 eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator
  结论: {s : Set R}
  证明: eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hsN (span_smul_eq s N).symm) (span_le.mpr hsJac)

Depends on / 依赖: Eq.trans, eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator, span_le, span_le.mpr, span_smul_eq
-/
lemma eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator {s : Set R}
    {N : Submodule R M} (hN : FG N) (hsN : N = s • N)
    (hsJac : s subseteq N.annihilator.jacobson) : N = ⊥ :=
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hsN (span_smul_eq s N).symm) (span_le.mpr hsJac)

/--
lemma `top_ne_ideal_smul_of_le_jacobson_annihilator` / 引理 `top_ne_ideal_smul_of_le_jacobson_annihilator`

English:
lemma top_ne_ideal_smul_of_le_jacobson_annihilator
  statement: [Nontrivial M]
  proof: fun H => top_ne_bot
eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator Module.Finite.fg_top H
    (congrArg (I <= Ideal.jacobson ·) annihilator_top).mpr h

中文:
引理 top_ne_ideal_smul_of_le_jacobson_annihilator
  结论: [Nontrivial M]
  证明: fun H => top_ne_bot
eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator Module.Finite.fg_top H
    (congrArg (I <= Ideal.jacobson ·) annihilator_top).mpr h

Depends on / 依赖: top_ne_bot
-/
lemma top_ne_ideal_smul_of_le_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {I} (h : I <= (Module.annihilator R M).jacobson) :
(⊤ : Submodule R M) != I • ⊤ := fun H => top_ne_bot
eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator Module.Finite.fg_top H
    (congrArg (I <= Ideal.jacobson ·) annihilator_top).mpr h

open scoped Pointwise in
/--
lemma `top_ne_set_smul_of_subset_jacobson_annihilator` / 引理 `top_ne_set_smul_of_subset_jacobson_annihilator`

English:
lemma top_ne_set_smul_of_subset_jacobson_annihilator
  statement: [Nontrivial M]
  proof: ne_of_ne_of_eq (top_ne_ideal_smul_of_le_jacobson_annihilator (span_le.mpr h))
    (span_smul_eq _ _)

中文:
引理 top_ne_set_smul_of_subset_jacobson_annihilator
  结论: [Nontrivial M]
  证明: ne_of_ne_of_eq (top_ne_ideal_smul_of_le_jacobson_annihilator (span_le.mpr h))
    (span_smul_eq _ _)

Depends on / 依赖: ne_of_ne_of_eq, span_le, span_le.mpr, span_smul_eq, top_ne_ideal_smul_of_le_jacobson_annihilator
-/
lemma top_ne_set_smul_of_subset_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {s : Set R}
    (h : s subseteq (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) != s • ⊤ :=
  ne_of_ne_of_eq (top_ne_ideal_smul_of_le_jacobson_annihilator (span_le.mpr h))
    (span_smul_eq _ _)

open scoped Pointwise in
/--
lemma `top_ne_pointwise_smul_of_mem_jacobson_annihilator` / 引理 `top_ne_pointwise_smul_of_mem_jacobson_annihilator`

English:
lemma top_ne_pointwise_smul_of_mem_jacobson_annihilator
  statement: [Nontrivial M]
  proof: ne_of_ne_of_eq (top_ne_set_smul_of_subset_jacobson_annihilator <|
                    Set.singleton_subset_iff.mpr h) (singleton_set_smul ⊤ r)

中文:
引理 top_ne_pointwise_smul_of_mem_jacobson_annihilator
  结论: [Nontrivial M]
  证明: ne_of_ne_of_eq (top_ne_set_smul_of_subset_jacobson_annihilator <|
                    Set.singleton_subset_iff.mpr h) (singleton_set_smul ⊤ r)

Depends on / 依赖: Set.singleton_subset_iff.mpr, ne_of_ne_of_eq, singleton_set_smul, singleton_subset_iff, top_ne_set_smul_of_subset_jacobson_annihilator
-/
lemma top_ne_pointwise_smul_of_mem_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {r} (h : r in (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) != r • ⊤ :=
  ne_of_ne_of_eq (top_ne_set_smul_of_subset_jacobson_annihilator <|
                    Set.singleton_subset_iff.mpr h) (singleton_set_smul ⊤ r)

/-- **Nakayama's Lemma** - Statement (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
@[stacks 00DV "(2)"]
/--
theorem `eq_bot_of_le_smul_of_le_jacobson_bot` / 定理 `eq_bot_of_le_smul_of_le_jacobson_bot`

English:
theorem eq_bot_of_le_smul_of_le_jacobson_bot
  statement: (I : Ideal R) (N : Submodule R M) (hN : N.FG)
  proof: by
  rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac]; rw [Submodule.bot_smul]

中文:
定理 eq_bot_of_le_smul_of_le_jacobson_bot
  结论: (I : Ideal R) (N : Submodule R M) (hN : N.FG)
  证明: by
  rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac]; rw [Submodule.bot_smul]

Depends on / 依赖: Submodule, Submodule.bot_smul, bot_smul, eq_smul_of_le_smul_of_le_jacobson
-/
theorem eq_bot_of_le_smul_of_le_jacobson_bot (I : Ideal R) (N : Submodule R M) (hN : N.FG)
    (hIN : N <= I • N) (hIjac : I <= jacobson ⊥) : N = ⊥ := by
  rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac]; rw [Submodule.bot_smul]

/--
theorem `sup_eq_sup_smul_of_le_smul_of_le_jacobson` / 定理 `sup_eq_sup_smul_of_le_smul_of_le_jacobson`

English:
theorem sup_eq_sup_smul_of_le_smul_of_le_jacobson
  statement: {I J : Ideal R} {N N' : Submodule R M}
  proof: by
  have hNN' : N ⊔ N' = N ⊔ I • N' :=
    le_antisymm (sup_le le_sup_left hNN)
    (sup_le_sup_left (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _)
  have h_comap :=
    comap_injective_of_surjective (LinearMap.range_eq_top.1 N.range_mkQ)
  have : (I • N').map N.mkQ = N'.map N.mkQ := 

中文:
定理 sup_eq_sup_smul_of_le_smul_of_le_jacobson
  结论: {I J : Ideal R} {N N' : Submodule R M}
  证明: by
  have hNN' : N ⊔ N' = N ⊔ I • N' :=
    le_antisymm (sup_le le_sup_left hNN)
    (sup_le_sup_left (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _)
  have h_comap :=
    comap_injective_of_surjective (LinearMap.range_eq_top.1 N.range_mkQ)
  have : (I • N').map N.mkQ = N'.map N.mkQ := 

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, N.mkQ, N.range_mkQ, Submodule, Submodule.eq_smul_of_le_smul_of_le_jacobson, Submodule.smul_le, Submodule.smul_mem, comap_injective_of_surjective, comap_map_mkQ, eq_comm, eq_iff, eq_smul_of_le_smul_of_le_jacobson, h_comap, h_comap.eq_iff, le_antisymm, le_sup_left, map_sm, map_smul, range_eq_top
-/
theorem sup_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
    (hN' : N'.FG) (hIJ : I <= jacobson J) (hNN : N' <= N ⊔ I • N') : N ⊔ N' = N ⊔ J • N' := by
  have hNN' : N ⊔ N' = N ⊔ I • N' :=
    le_antisymm (sup_le le_sup_left hNN)
    (sup_le_sup_left (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _)
  have h_comap :=
    comap_injective_of_surjective (LinearMap.range_eq_top.1 N.range_mkQ)
  have : (I • N').map N.mkQ = N'.map N.mkQ := by
    simpa only [← h_comap.eq_iff, comap_map_mkQ, sup_comm, eq_comm] using hNN'
  have :=
    @Submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J (N'.map N.mkQ) (hN'.map _)
      (by rw [← map_smul'', this]) hIJ
  rwa [← map_smul'', ← h_comap.eq_iff, comap_map_eq, comap_map_eq, Submodule.ker_mkQ, sup_comm,
    sup_comm (b := N)] at this

/-- **Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_le_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`. -/
@[stacks 00DV "(4)"]
/--
theorem `sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` / 定理 `sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson`

English:
theorem sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson
  statement: {I J : Ideal R} {N N' : Submodule R M}
  proof: ((sup_le_sup_left smul_le_right _).antisymm (sup_le le_sup_left hNN)).trans
    (sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN)

中文:
定理 sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson
  结论: {I J : Ideal R} {N N' : Submodule R M}
  证明: ((sup_le_sup_left smul_le_right _).antisymm (sup_le le_sup_left hNN)).trans
    (sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN)

Depends on / 依赖: antisymm, le_sup_left, smul_le_right, sup_eq_sup_smul_of_le_smul_of_le_jacobson, sup_le, sup_le_sup_left
-/
theorem sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
    (hN' : N'.FG) (hIJ : I <= jacobson J) (hNN : N' <= N ⊔ I • N') : N ⊔ I • N' = N ⊔ J • N' :=
  ((sup_le_sup_left smul_le_right _).antisymm (sup_le le_sup_left hNN)).trans
    (sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN)

/--
theorem `le_of_le_smul_of_le_jacobson_bot` / 定理 `le_of_le_smul_of_le_jacobson_bot`

English:
theorem le_of_le_smul_of_le_jacobson_bot
  statement: {R M} [CommRing R] [AddCommGroup M] [Module R M]
  proof: by
  rw [← sup_eq_left]; rw [sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN]; rw [bot_smul]; rw [sup_bot_eq]

中文:
定理 le_of_le_smul_of_le_jacobson_bot
  结论: {R M} [CommRing R] [AddCommGroup M] [Module R M]
  证明: by
  rw [← sup_eq_left]; rw [sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN]; rw [bot_smul]; rw [sup_bot_eq]

Depends on / 依赖: bot_smul, sup_bot_eq, sup_eq_left, sup_eq_sup_smul_of_le_smul_of_le_jacobson
-/
theorem le_of_le_smul_of_le_jacobson_bot {R M} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I <= jacobson ⊥) (hNN : N' <= N ⊔ I • N') : N' <= N := by
  rw [← sup_eq_left]; rw [sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN]; rw [bot_smul]; rw [sup_bot_eq]

/-- **Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
@[stacks 00DV "(4)"]
/--
theorem `smul_le_of_le_smul_of_le_jacobson_bot` / 定理 `smul_le_of_le_smul_of_le_jacobson_bot`

English:
theorem smul_le_of_le_smul_of_le_jacobson_bot
  statement: {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
  proof: smul_le_right.trans (le_of_le_smul_of_le_jacobson_bot hN' hIJ hNN)

中文:
定理 smul_le_of_le_smul_of_le_jacobson_bot
  结论: {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
  证明: smul_le_right.trans (le_of_le_smul_of_le_jacobson_bot hN' hIJ hNN)

Depends on / 依赖: le_of_le_smul_of_le_jacobson_bot, smul_le_right, smul_le_right.trans
-/
theorem smul_le_of_le_smul_of_le_jacobson_bot {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I <= jacobson ⊥) (hNN : N' <= N ⊔ I • N') : I • N' <= N :=
  smul_le_right.trans (le_of_le_smul_of_le_jacobson_bot hN' hIJ hNN)

open scoped Pointwise in
@[stacks 00DV "(3) see `Submodule.localized₀_le_localized₀_of_smul_le` for the second conclusion."]
/--
lemma `exists_sub_one_mem_and_smul_le_of_fg_of_le_sup` / 引理 `exists_sub_one_mem_and_smul_le_of_fg_of_le_sup`

English:
lemma exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
  statement: {I : Ideal R}
  proof: by
  have hNN'' : P <= N ⊔ N' := le_trans hNN' (by simpa using le_trans smul_le_right le_sup_right)
  have h1 : P.map N.mkQ = N'.map N.mkQ := by
    refine le_antisymm ?_ (map_mono hN'le)
    simpa using map_mono (f := N.mkQ) hNN''
  have h2 : P.map N.mkQ = (I • N').map N.mkQ := by
    apply le_anti

中文:
引理 exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
  结论: {I : Ideal R}
  证明: by
  have hNN'' : P <= N ⊔ N' := le_trans hNN' (by simpa using le_trans smul_le_right le_sup_right)
  have h1 : P.map N.mkQ = N'.map N.mkQ := by
    refine le_antisymm ?_ (map_mono hN'le)
    simpa using map_mono (f := N.mkQ) hNN''
  have h2 : P.map N.mkQ = (I • N').map N.mkQ := by
    apply le_anti

Depends on / 依赖: N.mkQ, P.map, conv_lhs, exists_sub_one_mem_and_smul_eq_zero, le_antisymm, le_sup_right, le_trans, map_mono, smul_le_right
-/
lemma exists_sub_one_mem_and_smul_le_of_fg_of_le_sup {I : Ideal R}
    {N N' P : Submodule R M} (hN' : N'.FG) (hN'le : N' <= P) (hNN' : P <= N ⊔ I • N') :
    exists r : R, r - 1 in I ∧ r • P <= N := by
  have hNN'' : P <= N ⊔ N' := le_trans hNN' (by simpa using le_trans smul_le_right le_sup_right)
  have h1 : P.map N.mkQ = N'.map N.mkQ := by
    refine le_antisymm ?_ (map_mono hN'le)
    simpa using map_mono (f := N.mkQ) hNN''
  have h2 : P.map N.mkQ = (I • N').map N.mkQ := by
    apply le_antisymm
    · simpa using map_mono (f := N.mkQ) hNN'
    · rw [h1]
      simp [smul_le_right]
  have hle : (P.map N.mkQ) <= I • P.map N.mkQ := by
    conv_lhs => rw [h2]
    simp [← h1]
  obtain ⟨r, hmem, hr⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I _
    (h1 ▸ hN'.map _) hle
  refine ⟨r, hmem, fun x hx => ?_⟩
  induction hx using Submodule.smul_inductionOn_pointwise with
  | smul₀ p hp =>
    rw [← Submodule.Quotient.mk_eq_zero]; rw [Quotient.mk_smul]
    exact hr _ ⟨p, hp, rfl⟩
  | smul₁ _ _ _ h => exact N.smul_mem _ h
  | add _ _ _ _ hx hy => exact N.add_mem hx hy
  | zero => exact N.zero_mem

/--
lemma `le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot` / 引理 `le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot`

English:
lemma le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot
  proof: by
  apply le_of_le_smul_of_le_jacobson_bot hN hIjac
  apply_fun comap (I • N).mkQ at hmaple
  on_goal 2 => apply Submodule.comap_mono
  simp only [comap_map_mkQ, smul_le_right, sup_of_le_right] at hmaple
  grw [sup_comm, ← hmaple]

@[deprecated (since := "2026-01-03")]
alias le_span_of_map_mkQ_le_m

中文:
引理 le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot
  证明: by
  apply le_of_le_smul_of_le_jacobson_bot hN hIjac
  apply_fun comap (I • N).mkQ at hmaple
  on_goal 2 => apply Submodule.comap_mono
  simp only [comap_map_mkQ, smul_le_right, sup_of_le_right] at hmaple
  grw [sup_comm, ← hmaple]

@[deprecated (since := "2026-01-03")]
alias le_span_of_map_mkQ_le_m

Depends on / 依赖: Submodule, Submodule.comap_mono, apply_fun, comap_map_mkQ, comap_mono, hmaple, le_of_le_smul_of_le_jacobson_bot, on_goal, smul_le_right, sup_comm, sup_of_le_right
-/
lemma le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N N' : Submodule R M} (hN : N.FG) (hIjac : I <= jacobson ⊥)
    (hmaple : map (I • N).mkQ N <= map (I • N).mkQ N') : N <= N' := by
  apply le_of_le_smul_of_le_jacobson_bot hN hIjac
  apply_fun comap (I • N).mkQ at hmaple
  on_goal 2 => apply Submodule.comap_mono
  simp only [comap_map_mkQ, smul_le_right, sup_of_le_right] at hmaple
  grw [sup_comm, ← hmaple]

@[deprecated (since := "2026-01-03")]
alias le_span_of_map_mkQ_le_map_mkQ_span_of_le_jacobson_bot :=
  le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot

/--
lemma `eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot` / 引理 `eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot`

English:
lemma eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot
  proof: by
  apply le_antisymm
  · exact le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot hN hIjac hmaple.le
  · apply_fun comap (I • N).mkQ at hmaple
    simp only [comap_map_mkQ, smul_le_right, sup_of_le_right] at hmaple
    rw [hmaple]; apply le_sup_right

中文:
引理 eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot
  证明: by
  apply le_antisymm
  · exact le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot hN hIjac hmaple.le
  · apply_fun comap (I • N).mkQ at hmaple
    simp only [comap_map_mkQ, smul_le_right, sup_of_le_right] at hmaple
    rw [hmaple]; apply le_sup_right

Depends on / 依赖: apply_fun, comap_map_mkQ, hmaple, hmaple.le, le_antisymm, le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot, le_sup_right, smul_le_right, sup_of_le_right
-/
lemma eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N N' : Submodule R M} (hN : N.FG) (hIjac : I <= jacobson ⊥)
    (hmaple : map (I • N).mkQ N = map (I • N).mkQ N') : N = N' := by
  apply le_antisymm
  · exact le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot hN hIjac hmaple.le
  · apply_fun comap (I • N).mkQ at hmaple
    simp only [comap_map_mkQ, smul_le_right, sup_of_le_right] at hmaple
    rw [hmaple]; apply le_sup_right

/--
**Nakayama's Lemma** - Statement (8) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).

If `N` is a finitely generated `R`-submodule of `M`,
`I` is an ideal contained in the Jacobson radical of `R`,
`s` is a set of `M / (I • N)` that spans the quotient image of `N`,
then there exists a spanning set `t` of `N` in bijection with `s` via the quotient map.
-/
@[stacks 00DV "(8)"]
/--
theorem `exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot` / 定理 `exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot`

English:
theorem exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot
  proof: by
  use Quotient.out '' s
  split_ands
  · simp [Set.InjOn]
  · simp [Set.image_image]
  · symm; apply eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot hN hIjac
    simp [← hsspan, map_span, Set.image_image]

中文:
定理 exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot
  证明: by
  use Quotient.out '' s
  split_ands
  · simp [Set.InjOn]
  · simp [Set.image_image]
  · symm; apply eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot hN hIjac
    simp [← hsspan, map_span, Set.image_image]

Depends on / 依赖: Quotient, Quotient.out, Set.InjOn, Set.image_image, eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot, hsspan, image_image, map_span, split_ands
-/
theorem exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N : Submodule R M} (s : Set (M ⧸ (I • N)))
    (hN : N.FG) (hIjac : I <= jacobson ⊥) (hsspan : span R s = map (I • N).mkQ N) :
    exists (t : Set M), t.InjOn (I • N).mkQ ∧ (I • N).mkQ '' t = s ∧ span R t = N := by
  use Quotient.out '' s
  split_ands
  · simp [Set.InjOn]
  · simp [Set.image_image]
  · symm; apply eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot hN hIjac
    simp [← hsspan, map_span, Set.image_image]

end Submodule

/--
lemma `LinearMap.surjective_of_surjective_comp_mkQ` / 引理 `LinearMap.surjective_of_surjective_comp_mkQ`

English:
lemma LinearMap.surjective_of_surjective_comp_mkQ
  statement: {N : Type*} [AddCommGroup N] [Module R N]
  proof: by
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›) Ile
  rw [top_le_iff]; rw [sup_comm]; rw [← Submodule.map_mkQ_eq_top]; rw [← LinearMap.range_comp]
  exact LinearMap.range_eq_top_of_surjective _ surj

中文:
引理 LinearMap.surjective_of_surjective_comp_mkQ
  结论: {N : 类型} [AddCommGroup N] [Module R N]
  证明: by
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›) Ile
  rw [top_le_iff]; rw [sup_comm]; rw [← Submodule.map_mkQ_eq_top]; rw [← LinearMap.range_comp]
  exact LinearMap.range_eq_top_of_surjective _ surj

Depends on / 依赖: LinearMap, LinearMap.range_comp, LinearMap.range_eq_top, LinearMap.range_eq_top_of_surjective, Module, Module.finite_def.mp, Submodule, Submodule.le_of_le_smul_of_le_jacobson_bot, Submodule.map_mkQ_eq_top, finite_def, le_of_le_smul_of_le_jacobson_bot, map_mkQ_eq_top, range_comp, range_eq_top, range_eq_top_of_surjective, sup_comm, top_le_iff
-/
lemma LinearMap.surjective_of_surjective_comp_mkQ {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N] (f : M ->ₗ[R] N) (I : Ideal R) (Ile : I <= (⊥ : Ideal R).jacobson)
    (surj : Function.Surjective ((I • (⊤ : Submodule R N)).mkQ ∘ₗ f)) : Function.Surjective f := by
  rw [← LinearMap.range_eq_top]; rw [← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›) Ile
  rw [top_le_iff]; rw [sup_comm]; rw [← Submodule.map_mkQ_eq_top]; rw [← LinearMap.range_comp]
  exact LinearMap.range_eq_top_of_surjective _ surj
