/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy of the image of a set under a semiconjugacy

Consider two dynamical systems `(X, S)` and `(Y, T)` together with a semiconjugacy `φ`:


```
X ---S--> X
| |
φ φ
| |
v v
Y ---T--> Y
```

We relate the topological entropy of a subset `F ⊆ X` with the topological entropy
of its image `φ '' F ⊆ Y`.

The best-known theorem is that, if all maps are uniformly continuous, then
`coverEntropy T (φ '' F) ≤ coverEntropy S F`. This is theorem
`coverEntropy_image_le_of_uniformContinuous` herein. We actually prove the much more general
statement that `coverEntropy T (φ '' F) = coverEntropy S F` if `X` is endowed with the pullback
by `φ` of the uniform structure of `Y`.

This more general statement has another direct consequence: if `F` is `S`-invariant, then the
topological entropy of the restriction of `S` to `F` is exactly `coverEntropy S F`. This
corollary is essential: in most references, the entropy of an invariant subset (or subsystem) `F` is
defined as the entropy of the restriction to `F` of the system. We chose instead to give a direct
definition of the topological entropy of a subset, so as to avoid working with subtypes. Theorem
`coverEntropy_restrict` shows that this choice is coherent with the literature.

## Implementation notes
We use only the definition of the topological entropy using covers; the simplest version of
`IsDynCoverOf.image` for nets fails.

## Main results
- `coverEntropy_image_of_comap`/`coverEntropyInf_image_of_comap`: the entropy of `φ '' F` equals
  the entropy of `F` if `X` is endowed with the pullback by `φ` of the uniform structure of `Y`.
- `coverEntropy_image_le_of_uniformContinuous`/`coverEntropyInf_image_le_of_uniformContinuous`:
  the entropy of `φ '' F` is lower than the entropy of `F` if `φ` is uniformly continuous.
- `coverEntropy_restrict`: the entropy of the restriction of `S` to an invariant set `F` is
  `coverEntropy S F`.

## Tags
entropy, semiconjugacy
-/

public section

open Function Prod Set Uniformity UniformSpace
open scoped SetRel

namespace Dynamics

variable {X Y : Type*} {s F : Set X} {V : SetRel Y Y} {S : X -> X} {T : Y -> Y} {φ : X -> Y} {n : Nat}

/--
lemma `IsDynCoverOf.image` / 引理 `IsDynCoverOf.image`

English:
lemma IsDynCoverOf.image
  given: (h : Semiconj φ S T) (h' : IsDynCoverOf S F (map φ φ ⁻¹' V) n s)
  proof: by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := h' hx
  refine ⟨_, Set.mem_image_of_mem _ hy, show (x, y) in map φ φ ⁻¹' dynEntourage T V n from ?_⟩
  rwa [h.preimage_dynEntourage V n]

中文:
引理 IsDynCoverOf.image
  条件: (h : Semiconj φ S T) (h' : IsDynCoverOf S F (map φ φ ⁻¹' V) n s)
  证明: by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := h' hx
  refine ⟨_, Set.mem_image_of_mem _ hy, show (x, y) in map φ φ ⁻¹' dynEntourage T V n from ?_⟩
  rwa [h.preimage_dynEntourage V n]

Depends on / 依赖: Set.mem_image_of_mem, dynEntourage, h.preimage_dynEntourage, mem_image_of_mem, preimage_dynEntourage
-/
lemma IsDynCoverOf.image (h : Semiconj φ S T) (h' : IsDynCoverOf S F (map φ φ ⁻¹' V) n s) :
    IsDynCoverOf T (φ '' F) V n (φ '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := h' hx
  refine ⟨_, Set.mem_image_of_mem _ hy, show (x, y) in map φ φ ⁻¹' dynEntourage T V n from ?_⟩
  rwa [h.preimage_dynEntourage V n]

/--
lemma `IsDynCoverOf.preimage` / 引理 `IsDynCoverOf.preimage`

English:
lemma IsDynCoverOf.preimage
  statement: (h : Semiconj φ S T) [V.IsSymm] {t : Finset Y}
  proof: by
  classical
  rcases isEmpty_or_nonempty X with _ | _
  · exact ⟨∅, eq_empty_of_isEmpty F ▸ ⟨isDynCoverOf_empty, Finset.card_empty ▸ zero_le⟩⟩
  -- If `t` is a dynamical cover of `φ '' F`, then we want to choose one preimage by `φ` for each
  -- element of `t`. This is complicated by the fact tha

中文:
引理 IsDynCoverOf.preimage
  结论: (h : Semiconj φ S T) [V.IsSymm] {t : Finset Y}
  证明: by
  classical
  rcases isEmpty_or_nonempty X with _ | _
  · exact ⟨∅, eq_empty_of_isEmpty F ▸ ⟨isDynCoverOf_empty, Finset.card_empty ▸ zero_le⟩⟩
  -- If `t` is a dynamical cover of `φ '' F`, then we want to choose one preimage by `φ` for each
  -- element of `t`. This is complicated by the fact tha

Depends on / 依赖: Finset, Finset.card_empty, card_empty, classical, eq_empty_of_isEmpty, isDynCoverOf_empty, isEmpty_or_nonempty, zero_le
-/
lemma IsDynCoverOf.preimage (h : Semiconj φ S T) [V.IsSymm] {t : Finset Y}
    (h' : IsDynCoverOf T (φ '' F) V n t) :
    exists s : Finset X, IsDynCoverOf S F ((map φ φ) ⁻¹' (V ○ V)) n s ∧ s.card <= t.card := by
  classical
  rcases isEmpty_or_nonempty X with _ | _
  · exact ⟨∅, eq_empty_of_isEmpty F ▸ ⟨isDynCoverOf_empty, Finset.card_empty ▸ zero_le⟩⟩
  -- If `t` is a dynamical cover of `φ '' F`, then we want to choose one preimage by `φ` for each
  -- element of `t`. This is complicated by the fact that `t` may not be a subset of `φ '' F`,
  -- and may not even be in the range of `φ`. Hence, we first modify `t` to make it a subset
  -- of `φ '' F`. This requires taking larger entourages.
  obtain ⟨s, s_cover, s_card, s_inter⟩ := h'.nonempty_inter
  choose! g g_rel g_mem using fun (x : Y) (h : x in s) => nonempty_def.1 (s_inter x h)
  choose! f _ φ_f using fun (y : Y) (hy : y in φ '' F) => hy
  refine ⟨s.image (f ∘ g), fun x hx => ?_, Finset.card_image_le.trans s_card⟩
  simp only [Finset.coe_image, comp_apply, mem_image, SetLike.mem_coe, ← h.preimage_dynEntourage,
    mem_preimage, map_apply, exists_exists_and_eq_and]
  obtain ⟨y, hy, hxy⟩ := s_cover (Set.mem_image_of_mem _ hx)
  refine ⟨y, hy, dynEntourage_comp_subset _ _ _ _ ⟨_, hxy, ?_⟩⟩
  rw [φ_f _ (g_mem _ hy)]
  exact g_rel _ hy

/--
lemma `le_coverMincard_image` / 引理 `le_coverMincard_image`

English:
lemma le_coverMincard_image
  given: (h : Semiconj φ S T) (F : Set X) [V.IsSymm] (n : Nat)
  proof: by
  rcases eq_top_or_lt_top (coverMincard T (φ '' F) V n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨t, t_cover, t_card⟩ := (coverMincard_finite_iff T (φ '' F) V n).1 h'
  obtain ⟨s, s_cover, s_card⟩ := t_cover.preimage h
  rw [← t_card]
  exact s_cover.coverMincard_le_card.trans (WithTop.coe_le_

中文:
引理 le_coverMincard_image
  条件: (h : Semiconj φ S T) (F : Set X) [V.IsSymm] (n : 自然数)
  证明: by
  rcases eq_top_or_lt_top (coverMincard T (φ '' F) V n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨t, t_cover, t_card⟩ := (coverMincard_finite_iff T (φ '' F) V n).1 h'
  obtain ⟨s, s_cover, s_card⟩ := t_cover.preimage h
  rw [← t_card]
  exact s_cover.coverMincard_le_card.trans (WithTop.coe_le_

Depends on / 依赖: WithTop, WithTop.coe_le_coe, coe_le_coe, coverMincard, coverMincard_finite_iff, coverMincard_le_card, eq_top_or_lt_top, le_top, preimage, s_card, s_cover, s_cover.coverMincard_le_card.trans, t_card, t_cover, t_cover.preimage
-/
lemma le_coverMincard_image (h : Semiconj φ S T) (F : Set X) [V.IsSymm] (n : Nat) :
    coverMincard S F ((map φ φ) ⁻¹' (V ○ V)) n <= coverMincard T (φ '' F) V n := by
  rcases eq_top_or_lt_top (coverMincard T (φ '' F) V n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨t, t_cover, t_card⟩ := (coverMincard_finite_iff T (φ '' F) V n).1 h'
  obtain ⟨s, s_cover, s_card⟩ := t_cover.preimage h
  rw [← t_card]
  exact s_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 s_card)

/--
lemma `coverMincard_image_le` / 引理 `coverMincard_image_le`

English:
lemma coverMincard_image_le
  given: (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) (n : Nat)
  proof: by
  classical
  rcases eq_top_or_lt_top (coverMincard S F ((map φ φ) ⁻¹' V) n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_card⟩ := (coverMincard_finite_iff S F ((map φ φ) ⁻¹' V) n).1 h'
  rw [← s_card]
  have := s_cover.image h
  rw [← s.coe_image] at this
  exact this.coverMincard_

中文:
引理 coverMincard_image_le
  条件: (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) (n : 自然数)
  证明: by
  classical
  rcases eq_top_or_lt_top (coverMincard S F ((map φ φ) ⁻¹' V) n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_card⟩ := (coverMincard_finite_iff S F ((map φ φ) ⁻¹' V) n).1 h'
  rw [← s_card]
  have := s_cover.image h
  rw [← s.coe_image] at this
  exact this.coverMincard_

Depends on / 依赖: WithTop, WithTop.coe_le_coe, card_image_le, classical, coe_image, coe_le_coe, coverMincard, coverMincard_finite_iff, coverMincard_le_card, eq_top_or_lt_top, le_top, s.card_image_le, s.coe_image, s_card, s_cover, s_cover.image, this.coverMincard_le_card.trans
-/
lemma coverMincard_image_le (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) (n : Nat) :
    coverMincard T (φ '' F) V n <= coverMincard S F ((map φ φ) ⁻¹' V) n := by
  classical
  rcases eq_top_or_lt_top (coverMincard S F ((map φ φ) ⁻¹' V) n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_card⟩ := (coverMincard_finite_iff S F ((map φ φ) ⁻¹' V) n).1 h'
  rw [← s_card]
  have := s_cover.image h
  rw [← s.coe_image] at this
  exact this.coverMincard_le_card.trans (WithTop.coe_le_coe.2 s.card_image_le)

open ENNReal EReal ExpGrowth Filter

/--
lemma `le_coverEntropyEntourage_image` / 引理 `le_coverEntropyEntourage_image`

English:
lemma le_coverEntropyEntourage_image
  given: (h : Semiconj φ S T) (F : Set X) [V.IsSymm]
  proof: expGrowthSup_monotone fun n => ENat.toENNReal_mono (le_coverMincard_image h F n)

中文:
引理 le_coverEntropyEntourage_image
  条件: (h : Semiconj φ S T) (F : Set X) [V.IsSymm]
  证明: expGrowthSup_monotone fun n => ENat.toENNReal_mono (le_coverMincard_image h F n)

Depends on / 依赖: ENat.toENNReal_mono, expGrowthSup_monotone, le_coverMincard_image, toENNReal_mono
-/
lemma le_coverEntropyEntourage_image (h : Semiconj φ S T) (F : Set X) [V.IsSymm] :
    coverEntropyEntourage S F ((map φ φ) ⁻¹' (V ○ V)) <= coverEntropyEntourage T (φ '' F) V :=
  expGrowthSup_monotone fun n => ENat.toENNReal_mono (le_coverMincard_image h F n)

/--
lemma `le_coverEntropyInfEntourage_image` / 引理 `le_coverEntropyInfEntourage_image`

English:
lemma le_coverEntropyInfEntourage_image
  given: (h : Semiconj φ S T) (F : Set X) [V.IsSymm]
  proof: expGrowthInf_monotone fun n => ENat.toENNReal_mono (le_coverMincard_image h F n)

中文:
引理 le_coverEntropyInfEntourage_image
  条件: (h : Semiconj φ S T) (F : Set X) [V.IsSymm]
  证明: expGrowthInf_monotone fun n => ENat.toENNReal_mono (le_coverMincard_image h F n)

Depends on / 依赖: ENat.toENNReal_mono, expGrowthInf_monotone, le_coverMincard_image, toENNReal_mono
-/
lemma le_coverEntropyInfEntourage_image (h : Semiconj φ S T) (F : Set X) [V.IsSymm] :
    coverEntropyInfEntourage S F ((map φ φ) ⁻¹' (V ○ V)) <= coverEntropyInfEntourage T (φ '' F) V :=
  expGrowthInf_monotone fun n => ENat.toENNReal_mono (le_coverMincard_image h F n)

/--
lemma `coverEntropyEntourage_image_le` / 引理 `coverEntropyEntourage_image_le`

English:
lemma coverEntropyEntourage_image_le
  given: (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y)
  proof: expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_image_le h F V n)

中文:
引理 coverEntropyEntourage_image_le
  条件: (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y)
  证明: expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_image_le h F V n)

Depends on / 依赖: ENat.toENNReal_mono, coverMincard_image_le, expGrowthSup_monotone, toENNReal_mono
-/
lemma coverEntropyEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) :
    coverEntropyEntourage T (φ '' F) V <= coverEntropyEntourage S F ((map φ φ) ⁻¹' V) :=
  expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_image_le h F V n)

/--
lemma `coverEntropyInfEntourage_image_le` / 引理 `coverEntropyInfEntourage_image_le`

English:
lemma coverEntropyInfEntourage_image_le
  given: (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y)
  proof: expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_image_le h F V n)

中文:
引理 coverEntropyInfEntourage_image_le
  条件: (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y)
  证明: expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_image_le h F V n)

Depends on / 依赖: ENat.toENNReal_mono, coverMincard_image_le, expGrowthInf_monotone, toENNReal_mono
-/
lemma coverEntropyInfEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : SetRel Y Y) :
    coverEntropyInfEntourage T (φ '' F) V <= coverEntropyInfEntourage S F ((map φ φ) ⁻¹' V) :=
  expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_image_le h F V n)

/--
theorem `coverEntropy_image_of_comap` / 定理 `coverEntropy_image_of_comap`

English:
theorem coverEntropy_image_of_comap
  statement: (u : UniformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y}
  proof: by
  let : UniformSpace X := comap φ u
  apply le_antisymm
  · refine iSup₂_le fun V V_uni =>
(coverEntropyEntourage_antitone _ _ SetRel.symmetrize_subset_self).trans
      (coverEntropyEntourage_image_le h F _).trans ?_
    apply coverEntropyEntourage_le_coverEntropy
    rw [uniformity_comap φ]; rw

中文:
定理 coverEntropy_image_of_comap
  结论: (u : UniformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y}
  证明: by
  let : UniformSpace X := comap φ u
  apply le_antisymm
  · refine iSup₂_le fun V V_uni =>
(coverEntropyEntourage_antitone _ _ SetRel.symmetrize_subset_self).trans
      (coverEntropyEntourage_image_le h F _).trans ?_
    apply coverEntropyEntourage_le_coverEntropy
    rw [uniformity_comap φ]; rw

Depends on / 依赖: SetRel, SetRel.symmetrize_subset_self, U_uni, UniformSpace, V_sub, V_uni, W_symm, W_uni, coverEntropyEntourage_antitone, coverEntropyEntourage_image_le, coverEntropyEntourage_le_coverEntropy, le_antisymm, mem_comap, symmetrize_mem_uniformity, symmetrize_subset_self, uniformity_comap
-/
theorem coverEntropy_image_of_comap (u : UniformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropy T (φ '' F) = @coverEntropy X (comap φ u) S F := by
  let : UniformSpace X := comap φ u
  apply le_antisymm
  · refine iSup₂_le fun V V_uni =>
(coverEntropyEntourage_antitone _ _ SetRel.symmetrize_subset_self).trans
      (coverEntropyEntourage_image_le h F _).trans ?_
    apply coverEntropyEntourage_le_coverEntropy
    rw [uniformity_comap φ]; rw [mem_comap]
    exact ⟨_, symmetrize_mem_uniformity V_uni, .rfl⟩
  · refine iSup₂_le fun U U_uni => ?_
    simp only [uniformity_comap φ, mem_comap] at U_uni
    obtain ⟨V, V_uni, V_sub⟩ := U_uni
    obtain ⟨W, W_uni, W_symm, W_V⟩ := comp_symm_mem_uniformity_sets V_uni
    apply (coverEntropyEntourage_antitone S F ((preimage_mono W_V).trans V_sub)).trans
    apply (le_coverEntropyEntourage_image h F).trans
    exact coverEntropyEntourage_le_coverEntropy T (φ '' F) W_uni

/--
theorem `coverEntropyInf_image_of_comap` / 定理 `coverEntropyInf_image_of_comap`

English:
theorem coverEntropyInf_image_of_comap
  statement: (u : UniformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y}
  proof: by
  let : UniformSpace X := comap φ u
  apply le_antisymm
  · refine iSup₂_le fun V V_uni =>
(coverEntropyInfEntourage_antitone _ _ SetRel.symmetrize_subset_self).trans
      (coverEntropyInfEntourage_image_le h F _).trans ?_
    apply coverEntropyInfEntourage_le_coverEntropyInf
    rw [uniformity_

中文:
定理 coverEntropyInf_image_of_comap
  结论: (u : UniformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y}
  证明: by
  let : UniformSpace X := comap φ u
  apply le_antisymm
  · refine iSup₂_le fun V V_uni =>
(coverEntropyInfEntourage_antitone _ _ SetRel.symmetrize_subset_self).trans
      (coverEntropyInfEntourage_image_le h F _).trans ?_
    apply coverEntropyInfEntourage_le_coverEntropyInf
    rw [uniformity_

Depends on / 依赖: SetRel, SetRel.symmetrize_subset_self, U_uni, UniformSpace, V_sub, V_uni, W_symm, W_uni, coverEntropyInfEntourage_antitone, coverEntropyInfEntourage_image_le, coverEntropyInfEntourage_le_coverEntropyInf, le_antisymm, mem_comap, symmetrize_mem_uniformity, symmetrize_subset_self, uniformity_comap
-/
theorem coverEntropyInf_image_of_comap (u : UniformSpace Y) {S : X -> X} {T : Y -> Y} {φ : X -> Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropyInf T (φ '' F) = @coverEntropyInf X (comap φ u) S F := by
  let : UniformSpace X := comap φ u
  apply le_antisymm
  · refine iSup₂_le fun V V_uni =>
(coverEntropyInfEntourage_antitone _ _ SetRel.symmetrize_subset_self).trans
      (coverEntropyInfEntourage_image_le h F _).trans ?_
    apply coverEntropyInfEntourage_le_coverEntropyInf
    rw [uniformity_comap φ]; rw [mem_comap]
    exact ⟨_, symmetrize_mem_uniformity V_uni, .rfl⟩
  · refine iSup₂_le fun U U_uni => ?_
    simp only [uniformity_comap φ, mem_comap] at U_uni
    obtain ⟨V, V_uni, V_sub⟩ := U_uni
    obtain ⟨W, W_uni, W_symm, W_V⟩ := comp_symm_mem_uniformity_sets V_uni
    apply (coverEntropyInfEntourage_antitone S F ((preimage_mono W_V).trans V_sub)).trans
    apply (le_coverEntropyInfEntourage_image h F).trans
    exact coverEntropyInfEntourage_le_coverEntropyInf T (φ '' F) W_uni

open Subtype

/--
lemma `coverEntropy_restrict_subset` / 引理 `coverEntropy_restrict_subset`

English:
lemma coverEntropy_restrict_subset
  statement: [UniformSpace X] {T : X -> X} {F G : Set X} (hF : F subseteq G)
  proof: by
  rw [← coverEntropy_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F)]; rw [image_preimage_coe G F]; rw [inter_eq_right.2 hF]

中文:
引理 coverEntropy_restrict_subset
  结论: [UniformSpace X] {T : X -> X} {F G : Set X} (hF : F subseteq G)
  证明: by
  rw [← coverEntropy_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F)]; rw [image_preimage_coe G F]; rw [inter_eq_right.2 hF]

Depends on / 依赖: coverEntropy_image_of_comap, hG.val_restrict_apply, image_preimage_coe, inter_eq_right, val_restrict_apply
-/
lemma coverEntropy_restrict_subset [UniformSpace X] {T : X -> X} {F G : Set X} (hF : F subseteq G)
    (hG : MapsTo T G G) :
    coverEntropy (hG.restrict T G G) (val ⁻¹' F) = coverEntropy T F := by
  rw [← coverEntropy_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F)]; rw [image_preimage_coe G F]; rw [inter_eq_right.2 hF]

/--
lemma `coverEntropyInf_restrict_subset` / 引理 `coverEntropyInf_restrict_subset`

English:
lemma coverEntropyInf_restrict_subset
  statement: [UniformSpace X] {T : X -> X} {F G : Set X} (hF : F subseteq G)
  proof: by
  rw [← coverEntropyInf_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F)]; rw [image_preimage_coe G F]; rw [inter_eq_right.2 hF]

中文:
引理 coverEntropyInf_restrict_subset
  结论: [UniformSpace X] {T : X -> X} {F G : Set X} (hF : F subseteq G)
  证明: by
  rw [← coverEntropyInf_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F)]; rw [image_preimage_coe G F]; rw [inter_eq_right.2 hF]

Depends on / 依赖: coverEntropyInf_image_of_comap, hG.val_restrict_apply, image_preimage_coe, inter_eq_right, val_restrict_apply
-/
lemma coverEntropyInf_restrict_subset [UniformSpace X] {T : X -> X} {F G : Set X} (hF : F subseteq G)
    (hG : MapsTo T G G) :
    coverEntropyInf (hG.restrict T G G) (val ⁻¹' F) = coverEntropyInf T F := by
  rw [← coverEntropyInf_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F)]; rw [image_preimage_coe G F]; rw [inter_eq_right.2 hF]

/--
theorem `coverEntropy_restrict` / 定理 `coverEntropy_restrict`

English:
theorem coverEntropy_restrict
  given: [UniformSpace X] {T : X -> X} {F : Set X} (h : MapsTo T F F)
  proof: by
  rw [← coverEntropy_restrict_subset Subset.rfl h]; rw [coe_preimage_self F]

中文:
定理 coverEntropy_restrict
  条件: [UniformSpace X] {T : X -> X} {F : Set X} (h : MapsTo T F F)
  证明: by
  rw [← coverEntropy_restrict_subset Subset.rfl h]; rw [coe_preimage_self F]

Depends on / 依赖: Subset, Subset.rfl, coe_preimage_self, coverEntropy_restrict_subset
-/
theorem coverEntropy_restrict [UniformSpace X] {T : X -> X} {F : Set X} (h : MapsTo T F F) :
    coverEntropy (h.restrict T F F) univ = coverEntropy T F := by
  rw [← coverEntropy_restrict_subset Subset.rfl h]; rw [coe_preimage_self F]

/--
theorem `coverEntropy_image_le_of_uniformContinuous` / 定理 `coverEntropy_image_le_of_uniformContinuous`

English:
theorem coverEntropy_image_le_of_uniformContinuous
  statement: [UniformSpace X] [UniformSpace Y] {S : X -> X}
  proof: by
  rw [coverEntropy_image_of_comap _ h F]
  exact coverEntropy_antitone S F (uniformContinuous_iff_le_comap.1 h')

中文:
定理 coverEntropy_image_le_of_uniformContinuous
  结论: [UniformSpace X] [UniformSpace Y] {S : X -> X}
  证明: by
  rw [coverEntropy_image_of_comap _ h F]
  exact coverEntropy_antitone S F (uniformContinuous_iff_le_comap.1 h')

Depends on / 依赖: coverEntropy_antitone, coverEntropy_image_of_comap, uniformContinuous_iff_le_comap
-/
theorem coverEntropy_image_le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X -> X}
    {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) (h' : UniformContinuous φ) (F : Set X) :
    coverEntropy T (φ '' F) <= coverEntropy S F := by
  rw [coverEntropy_image_of_comap _ h F]
  exact coverEntropy_antitone S F (uniformContinuous_iff_le_comap.1 h')

/--
theorem `coverEntropyInf_image_le_of_uniformContinuous` / 定理 `coverEntropyInf_image_le_of_uniformContinuous`

English:
theorem coverEntropyInf_image_le_of_uniformContinuous
  statement: [UniformSpace X] [UniformSpace Y] {S : X -> X}
  proof: by
  rw [coverEntropyInf_image_of_comap _ h F]
  exact coverEntropyInf_antitone S F (uniformContinuous_iff_le_comap.1 h')

中文:
定理 coverEntropyInf_image_le_of_uniformContinuous
  结论: [UniformSpace X] [UniformSpace Y] {S : X -> X}
  证明: by
  rw [coverEntropyInf_image_of_comap _ h F]
  exact coverEntropyInf_antitone S F (uniformContinuous_iff_le_comap.1 h')

Depends on / 依赖: coverEntropyInf_antitone, coverEntropyInf_image_of_comap, uniformContinuous_iff_le_comap
-/
theorem coverEntropyInf_image_le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X -> X}
    {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) (h' : UniformContinuous φ) (F : Set X) :
    coverEntropyInf T (φ '' F) <= coverEntropyInf S F := by
  rw [coverEntropyInf_image_of_comap _ h F]
  exact coverEntropyInf_antitone S F (uniformContinuous_iff_le_comap.1 h')

/--
lemma `coverEntropy_image_le_of_uniformContinuousOn_invariant` / 引理 `coverEntropy_image_le_of_uniformContinuousOn_invariant`

English:
lemma coverEntropy_image_le_of_uniformContinuousOn_invariant
  statement: [UniformSpace X] [UniformSpace Y]
  proof: by
  rw [← coverEntropy_restrict_subset hF hG]
  have hφ : Semiconj (G.domRestrict φ) (hG.restrict S G G) T := by
    intro x
    rw [G.domRestrict_apply]; rw [G.domRestrict_apply]; rw [hG.val_restrict_apply]; rw [h.eq x]
  apply (coverEntropy_image_le_of_uniformContinuous hφ
    (uniformContinuousO

中文:
引理 coverEntropy_image_le_of_uniformContinuousOn_invariant
  结论: [UniformSpace X] [UniformSpace Y]
  证明: by
  rw [← coverEntropy_restrict_subset hF hG]
  have hφ : Semiconj (G.domRestrict φ) (hG.restrict S G G) T := by
    intro x
    rw [G.domRestrict_apply]; rw [G.domRestrict_apply]; rw [hG.val_restrict_apply]; rw [h.eq x]
  apply (coverEntropy_image_le_of_uniformContinuous hφ
    (uniformContinuousO

Depends on / 依赖: G.domRestrict, G.domRestrict_apply, Semiconj, coverEntropy_image_le_of_uniformContinuous, coverEntropy_restrict_subset, domRestrict, domRestrict_apply, h.eq, hG.restrict, hG.val_restrict_apply, image_image_val_eq_domRestrict_image, image_preimage_coe, inter_eq_right, restrict, trans_eq, uniformContinuousOn_iff_restrict, val_restrict_apply
-/
lemma coverEntropy_image_le_of_uniformContinuousOn_invariant [UniformSpace X] [UniformSpace Y]
    {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) {F G : Set X}
    (h' : UniformContinuousOn φ G) (hF : F subseteq G) (hG : MapsTo S G G) :
    coverEntropy T (φ '' F) <= coverEntropy S F := by
  rw [← coverEntropy_restrict_subset hF hG]
  have hφ : Semiconj (G.domRestrict φ) (hG.restrict S G G) T := by
    intro x
    rw [G.domRestrict_apply]; rw [G.domRestrict_apply]; rw [hG.val_restrict_apply]; rw [h.eq x]
  apply (coverEntropy_image_le_of_uniformContinuous hφ
    (uniformContinuousOn_iff_restrict.1 h') (val ⁻¹' F)).trans_eq'
  rw [← image_image_val_eq_domRestrict_image]; rw [image_preimage_coe G F]; rw [inter_eq_right.2 hF]

/--
lemma `coverEntropyInf_image_le_of_uniformContinuousOn_invariant` / 引理 `coverEntropyInf_image_le_of_uniformContinuousOn_invariant`

English:
lemma coverEntropyInf_image_le_of_uniformContinuousOn_invariant
  statement: [UniformSpace X] [UniformSpace Y]
  proof: by
  rw [← coverEntropyInf_restrict_subset hF hG]
  have hφ : Semiconj (G.domRestrict φ) (hG.restrict S G G) T := by
    intro a
    rw [G.domRestrict_apply]; rw [G.domRestrict_apply]; rw [hG.val_restrict_apply]; rw [h.eq a]
  apply (coverEntropyInf_image_le_of_uniformContinuous hφ
    (uniformConti

中文:
引理 coverEntropyInf_image_le_of_uniformContinuousOn_invariant
  结论: [UniformSpace X] [UniformSpace Y]
  证明: by
  rw [← coverEntropyInf_restrict_subset hF hG]
  have hφ : Semiconj (G.domRestrict φ) (hG.restrict S G G) T := by
    intro a
    rw [G.domRestrict_apply]; rw [G.domRestrict_apply]; rw [hG.val_restrict_apply]; rw [h.eq a]
  apply (coverEntropyInf_image_le_of_uniformContinuous hφ
    (uniformConti

Depends on / 依赖: G.domRestrict, G.domRestrict_apply, Semiconj, coverEntropyInf_image_le_of_uniformContinuous, coverEntropyInf_restrict_subset, domRestrict, domRestrict_apply, h.eq, hG.restrict, hG.val_restrict_apply, image_image_val_eq_domRestrict_image, image_preimage_coe, inter_eq_right, restrict, trans_eq, uniformContinuousOn_iff_restrict, val_restrict_apply
-/
lemma coverEntropyInf_image_le_of_uniformContinuousOn_invariant [UniformSpace X] [UniformSpace Y]
    {S : X -> X} {T : Y -> Y} {φ : X -> Y} (h : Semiconj φ S T) {F G : Set X}
    (h' : UniformContinuousOn φ G) (hF : F subseteq G) (hG : MapsTo S G G) :
    coverEntropyInf T (φ '' F) <= coverEntropyInf S F := by
  rw [← coverEntropyInf_restrict_subset hF hG]
  have hφ : Semiconj (G.domRestrict φ) (hG.restrict S G G) T := by
    intro a
    rw [G.domRestrict_apply]; rw [G.domRestrict_apply]; rw [hG.val_restrict_apply]; rw [h.eq a]
  apply (coverEntropyInf_image_le_of_uniformContinuous hφ
    (uniformContinuousOn_iff_restrict.1 h') (val ⁻¹' F)).trans_eq'
  rw [← image_image_val_eq_domRestrict_image]; rw [image_preimage_coe G F]; rw [inter_eq_right.2 hF]

end Dynamics
