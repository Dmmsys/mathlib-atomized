/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Analysis.Asymptotics.ExpGrowth
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Dynamics.TopologicalEntropy.DynamicalEntourage

/-!
# Topological entropy via covers

We implement Bowen-Dinaburg's definitions of the topological entropy, via covers.

All is stated in the vocabulary of uniform spaces. For compact spaces, the uniform structure
is canonical, so the topological entropy depends only on the topological structure. This will give
a clean proof that the topological entropy is a topological invariant of the dynamics.

A notable choice is that we define the topological entropy of a subset `F` of the whole space.
Usually, one defines the entropy of an invariant subset `F` as the entropy of the restriction of the
transformation to `F`. We avoid the latter definition as it would involve frequent manipulation of
subtypes. Our version directly gives a meaning to the topological entropy of a subsystem, and a
single theorem (`subset_restriction_entropy` in `TopologicalEntropy.Semiconj`) will give the
equivalence between both versions.

Another choice is to give a meaning to the entropy of `∅` (it must be `-∞` to stay coherent) and to
keep the possibility for the entropy to be infinite. Hence, the entropy takes values in the extended
reals `[-∞, +∞]`. The consequence is that we use `ℕ∞`, `ℝ≥0∞` and `EReal` numbers.

## Main definitions
- `IsDynCoverOf`: property that dynamical balls centered on a subset `s` cover a subset `F`.
- `coverMincard`: minimal cardinality of a dynamical cover. Takes values in `ℕ∞`.
- `coverEntropyInfEntourage`/`coverEntropyEntourage`: exponential growth of `coverMincard`.
  The former is defined with a `liminf`, the later with a `limsup`. Take values in `EReal`.
- `coverEntropyInf`/`coverEntropy`: supremum of `coverEntropyInfEntourage`/`coverEntropyEntourage`
  over all entourages (or limit as the entourages go to the diagonal). These are Bowen-Dinaburg's
  versions of the topological entropy with covers. Take values in `EReal`.

## Implementation notes
There are two competing definitions of topological entropy in this file: one uses a `liminf`,
the other a `limsup`. These two topological entropies are equal as soon as they are applied to an
invariant subset by theorem `coverEntropyInf_eq_coverEntropy`. We choose the default definition
to be the definition using a `limsup`, and give it the simpler name `coverEntropy` (instead of
`coverEntropySup`). Theorems about the topological entropy of invariant subsets will be stated
using only `coverEntropy`.

## Main results
- `IsDynCoverOf.iterate_le_pow`: given a dynamical cover at time `n`, creates dynamical covers
  at all iterates `n * m` with controlled cardinality.
- `IsDynCoverOf.coverEntropyEntourage_le_log_card_div`: upper bound on `coverEntropyEntourage`
  given any dynamical cover.
- `coverEntropyInf_eq_coverEntropy`: equality between the notions of topological entropy defined
  with a `liminf` and a `limsup`.

## Tags
cover, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

@[expose] public section

open Set SetRel Uniformity UniformSpace
open scoped Finset

namespace Dynamics

variable {X : Type*} {T : X -> X} {U V : SetRel X X} {n : Nat} {F s : Set X} {m n : Nat}

/-! ### Dynamical covers -/

/--
Definition of `IsDynCoverOf` / `IsDynCoverOf` 的定义

English:
definition IsDynCoverOf
  signature: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) (s : Set X)
  body: IsCover (dynEntourage T U n) F s

中文:
定义 IsDynCoverOf
  签名: (T : X -> X) (F : 集合 X) (U : SetRel X X) (n : 自然数) (s : 集合 X)
  定义体: IsCover (dynEntourage T U n) F s

Depends on / 依赖: IsCover, dynEntourage
-/
def IsDynCoverOf (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) (s : Set X) : Prop :=
  IsCover (dynEntourage T U n) F s

/--
lemma `IsDynCoverOf.of_le` / 引理 `IsDynCoverOf.of_le`

English:
lemma IsDynCoverOf.of_le
  given: (m_n : m <= n) (h : IsDynCoverOf T F U n s)
  statement: IsDynCoverOf T F U m s
  proof: h.mono_entourage by gcongr

中文:
引理 IsDynCoverOf.of_le
  条件: (m_n : m <= n) (h : IsDynCoverOf T F U n s)
  结论: IsDynCoverOf T F U m s
  证明: h.mono_entourage by gcongr

Depends on / 依赖: h.mono_entourage, mono_entourage
-/
lemma IsDynCoverOf.of_le (m_n : m <= n) (h : IsDynCoverOf T F U n s) : IsDynCoverOf T F U m s :=
h.mono_entourage by gcongr

/--
lemma `IsDynCoverOf.of_entourage_subset` / 引理 `IsDynCoverOf.of_entourage_subset`

English:
lemma IsDynCoverOf.of_entourage_subset
  given: (U_V : U subseteq V) (h : IsDynCoverOf T F U n s)
  proof: h.mono_entourage by gcongr

中文:
引理 IsDynCoverOf.of_entourage_subset
  条件: (U_V : U subseteq V) (h : IsDynCoverOf T F U n s)
  证明: h.mono_entourage by gcongr

Depends on / 依赖: h.mono_entourage, mono_entourage
-/
lemma IsDynCoverOf.of_entourage_subset (U_V : U subseteq V) (h : IsDynCoverOf T F U n s) :
IsDynCoverOf T F V n s := h.mono_entourage by gcongr

/--
lemma `isDynCoverOf_empty` / 引理 `isDynCoverOf_empty`

English:
lemma isDynCoverOf_empty
  statement: IsDynCoverOf T ∅ U n s
  proof: .empty

中文:
引理 isDynCoverOf_empty
  结论: IsDynCoverOf T ∅ U n s
  证明: .empty
-/
@[simp] lemma isDynCoverOf_empty : IsDynCoverOf T ∅ U n s := .empty

/--
lemma `isDynCoverOf_empty_right` / 引理 `isDynCoverOf_empty_right`

English:
lemma isDynCoverOf_empty_right
  statement: IsDynCoverOf T F U n ∅ ↔ F = ∅
  proof: by simp [IsDynCoverOf]

nonrec lemma IsDynCoverOf.nonempty (h : F.Nonempty) (h' : IsDynCoverOf T F U n s) : s.Nonempty :=
  h'.nonempty h

中文:
引理 isDynCoverOf_empty_right
  结论: IsDynCoverOf T F U n ∅ ↔ F = ∅
  证明: by simp [IsDynCoverOf]

nonrec lemma IsDynCoverOf.nonempty (h : F.Nonempty) (h' : IsDynCoverOf T F U n s) : s.Nonempty :=
  h'.nonempty h
-/
@[simp] lemma isDynCoverOf_empty_right : IsDynCoverOf T F U n ∅ ↔ F = ∅ := by simp [IsDynCoverOf]

nonrec lemma IsDynCoverOf.nonempty (h : F.Nonempty) (h' : IsDynCoverOf T F U n s) : s.Nonempty :=
  h'.nonempty h

/--
lemma `isDynCoverOf_zero` / 引理 `isDynCoverOf_zero`

English:
lemma isDynCoverOf_zero
  given: (T : X -> X) (F : Set X) (U : SetRel X X) (h : s.Nonempty)
  proof: by simp [IsDynCoverOf, h]

中文:
引理 isDynCoverOf_zero
  条件: (T : X -> X) (F : 集合 X) (U : SetRel X X) (h : s.非空)
  证明: by simp [IsDynCoverOf, h]

Depends on / 依赖: IsDynCoverOf
-/
lemma isDynCoverOf_zero (T : X -> X) (F : Set X) (U : SetRel X X) (h : s.Nonempty) :
    IsDynCoverOf T F U 0 s := by simp [IsDynCoverOf, h]

/--
lemma `isDynCoverOf_univ` / 引理 `isDynCoverOf_univ`

English:
lemma isDynCoverOf_univ
  given: (T : X -> X) (F : Set X) (n : Nat) (h : s.Nonempty)
  proof: by simp [IsDynCoverOf, h]

中文:
引理 isDynCoverOf_univ
  条件: (T : X -> X) (F : 集合 X) (n : 自然数) (h : s.非空)
  证明: by simp [IsDynCoverOf, h]

Depends on / 依赖: IsDynCoverOf
-/
lemma isDynCoverOf_univ (T : X -> X) (F : Set X) (n : Nat) (h : s.Nonempty) :
    IsDynCoverOf T F univ n s := by simp [IsDynCoverOf, h]

/--
lemma `IsDynCoverOf.nonempty_inter` / 引理 `IsDynCoverOf.nonempty_inter`

English:
lemma IsDynCoverOf.nonempty_inter
  given: [U.IsSymm] {s : Finset X} (h : IsDynCoverOf T F U n s)
  proof: by
  classical
  use {x in s | (ball x (dynEntourage T U n) inter F).Nonempty}
  simp only [Finset.coe_filter, Finset.mem_filter, and_imp, imp_self, implies_true, and_true]
  refine ⟨fun y y_F => ?_, Finset.card_mono (Finset.filter_subset _ s)⟩
  obtain ⟨z, z_s, y_Bz⟩ := h y_F
  exact ⟨z, ⟨z_s, _, (

中文:
引理 IsDynCoverOf.nonempty_inter
  条件: [U.是Symm] {s : 有限集 X} (h : IsDynCoverOf T F U n s)
  证明: by
  classical
  use {x in s | (ball x (dynEntourage T U n) inter F).Nonempty}
  simp only [Finset.coe_filter, Finset.mem_filter, and_imp, imp_self, implies_true, and_true]
  refine ⟨fun y y_F => ?_, Finset.card_mono (Finset.filter_subset _ s)⟩
  obtain ⟨z, z_s, y_Bz⟩ := h y_F
  exact ⟨z, ⟨z_s, _, (

Depends on / 依赖: Finset, Finset.card_mono, Finset.coe_filter, Finset.filter_subset, Finset.mem_filter, Nonempty, and_imp, and_true, card_mono, classical, coe_filter, dynEntourage, filter_subset, imp_self, implies_true, mem_filter, y_Bz
-/
lemma IsDynCoverOf.nonempty_inter [U.IsSymm] {s : Finset X} (h : IsDynCoverOf T F U n s) :
    exists t : Finset X, IsDynCoverOf T F U n t ∧ #t <= #s ∧
      forall x in t, (ball x (dynEntourage T U n) inter F).Nonempty := by
  classical
  use {x in s | (ball x (dynEntourage T U n) inter F).Nonempty}
  simp only [Finset.coe_filter, Finset.mem_filter, and_imp, imp_self, implies_true, and_true]
  refine ⟨fun y y_F => ?_, Finset.card_mono (Finset.filter_subset _ s)⟩
  obtain ⟨z, z_s, y_Bz⟩ := h y_F
  exact ⟨z, ⟨z_s, _, (dynEntourage T U n).symm y_Bz, y_F⟩, y_Bz⟩

/--
lemma `IsDynCoverOf.iterate_le_pow` / 引理 `IsDynCoverOf.iterate_le_pow`

English:
lemma IsDynCoverOf.iterate_le_pow
  statement: (F_inv : MapsTo T F F) [U.IsSymm] (n : Nat) {s : Finset X}
  proof: by
  classical
  -- Deal with the edge cases: `F = ∅` or `m = 0`.
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · exact ⟨∅, by simp⟩
  have _ : Nonempty X := F_nemp.nonempty
  have s_nemp := h.nonempty F_nemp
  obtain ⟨x, x_F⟩ := F_nemp
  rcases m.eq_zero_or_pos with rfl | m_pos
  · use {x}
  

中文:
引理 IsDynCoverOf.iterate_le_pow
  结论: (F_inv : 映射到 T F F) [U.是Symm] (n : 自然数) {s : 有限集 X}
  证明: by
  classical
  -- Deal with the edge cases: `F = ∅` or `m = 0`.
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · exact ⟨∅, by simp⟩
  have _ : Nonempty X := F_nemp.nonempty
  have s_nemp := h.nonempty F_nemp
  obtain ⟨x, x_F⟩ := F_nemp
  rcases m.eq_zero_or_pos with rfl | m_pos
  · use {x}
  

Depends on / 依赖: classical
-/
lemma IsDynCoverOf.iterate_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (n : Nat) {s : Finset X}
    (h : IsDynCoverOf T F U m s) :
    exists t : Finset X, IsDynCoverOf T F (U ○ U) (m * n) t ∧ t.card <= s.card ^ n := by
  classical
  -- Deal with the edge cases: `F = ∅` or `m = 0`.
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · exact ⟨∅, by simp⟩
  have _ : Nonempty X := F_nemp.nonempty
  have s_nemp := h.nonempty F_nemp
  obtain ⟨x, x_F⟩ := F_nemp
  rcases m.eq_zero_or_pos with rfl | m_pos
  · use {x}
    simp only [zero_mul, Finset.coe_singleton, Finset.card_singleton]
    exact ⟨isDynCoverOf_zero T F (U ○ U) (singleton_nonempty x),
      one_le_pow_of_one_le' (Nat.one_le_of_lt (Finset.Nonempty.card_pos s_nemp)) n⟩
  -- The proof goes as follows. Given an orbit of length `(m * n)` starting from `y`, each of its
  -- iterates `y`, `T^[m] y`, `T^[m]^[2] y` ... is `(dynEntourage T U m)`-close to a point of `s`.
  -- Conversely, given a sequence `t 0`, `t 1`, `t 2` of points in `s`, we choose a point
  -- `z = dyncover t` such that `z`, `T^[m] z`, `T^[m]^[2] z` ... are `(dynEntourage T U m)`-close
  -- to `t 0`, `t 1`, `t 2`... Then `y`, `T^[m] y`, `T^[m]^[2] y` ... are
  -- `(dynEntourage T (U ○ U) m)`-close to `z`, `T^[m] z`, `T^[m]^[2] z`, so that the union of such
  -- `z` provides the desired cover. Since there are at most `s.card ^ n` sequences of
  -- length `n` with values in `s`, we get the upper bound we want on the cardinality.
  -- First step: construct `dyncover`. Given `t 0`, `t 1`, `t 2`, if we cannot find such a point
  -- `dyncover t`, we use the dummy `x`.
  have (t : Fin n -> s) : exists y : X, (⋂ k : Fin n, T^[m * k] ⁻¹' ball (t k) (dynEntourage T U m)) subseteq
      ball y (dynEntourage T (U ○ U) (m * n)) := by
    rcases (⋂ k : Fin n, T^[m * k] ⁻¹' ball (t k) (dynEntourage T U m)).eq_empty_or_nonempty
      with inter_empt | inter_nemp
    · exact inter_empt ▸ ⟨x, empty_subset _⟩
    · obtain ⟨y, y_int⟩ := inter_nemp
      refine ⟨y, fun z z_int => ?_⟩
      simp only [ball, dynEntourage, Prod.map_iterate, mem_iInter, Set.mem_preimage, Prod.map_apply,
        mem_comp] at y_int z_int ⊢
      intro k k_mn
      replace k_mn := Nat.div_lt_of_lt_mul k_mn
      specialize z_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      specialize y_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      rw [← Function.iterate_add_apply T (k % m) (m * (k / m))]; rw [Nat.mod_add_div k m] at y_int z_int
      exact mem_comp_of_mem_ball y_int z_int
  choose! dyncover h_dyncover using this
  -- The cover we want is the set of all `dyncover t`, that is, `range dyncover`. We need to check
  -- that it is indeed a `(U ○ U, m * n)` cover, and that its cardinality is at most `card s ^ n`.
  -- Only the first point requires significant work.
  let sn := range dyncover
  refine ⟨sn.toFinset, ?_, ?_⟩
  · -- We implement the argument at the beginning: given `y ∈ F`, we extract `t 0`, `t 1`, `t 2`
    -- such that `y`, `T^[m] y`, `T^[m]^[2] y` ... is `(dynEntourage T U m)`-close to `t 0`, `t 1`,
    -- `t 2`... Then `dyncover t` is a point of `range dyncover` which satisfies the conclusion
    -- of the lemma.
    rw [Finset.coe_nonempty] at s_nemp
    have _ : Nonempty s := Finset.Nonempty.coe_sort s_nemp
    intro y y_F
    have key : forall k : Fin n, exists z : s, y in T^[m * k] ⁻¹' ball z (dynEntourage T U m) := by
      intro k
      have := h (MapsTo.iterate F_inv (m * k) y_F)
      simp only [Finset.mem_coe] at this
      obtain ⟨z, z_s, hz⟩ := this
      exact ⟨⟨z, z_s⟩, (dynEntourage T U m).symm hz⟩
    choose! t ht using key
    simp only [toFinset_range, Finset.coe_image, Finset.coe_univ, image_univ, mem_range,
      exists_exists_eq_and, sn]
refine ⟨t, (dynEntourage T (U ○ U) (m * n)).symm h_dyncover t by simpa using ht⟩
  · rw [toFinset_card]
    apply (Fintype.card_range_le dyncover).trans
    simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, le_refl]

/--
lemma `exists_isDynCoverOf_of_isCompact_uniformContinuous` / 引理 `exists_isDynCoverOf_of_isCompact_uniformContinuous`

English:
lemma exists_isDynCoverOf_of_isCompact_uniformContinuous
  statement: [UniformSpace X]
  proof: by
  obtain ⟨(V : SetRel X X), hV, hVsymm, hVU⟩ := symm_of_uniformity U_uni
  have uni_ite := dynEntourage_mem_uniformity h hV n
  let openCover x := ball x (dynEntourage T V n)
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover openCover fun x _ => ball_mem_nhds x uni_ite
exact ⟨s, .of_entourage

中文:
引理 存在_isDynCoverOf_of_isCompact_uniformContinuous
  结论: [一致空间 X]
  证明: by
  obtain ⟨(V : SetRel X X), hV, hVsymm, hVU⟩ := symm_of_uniformity U_uni
  have uni_ite := dynEntourage_mem_uniformity h hV n
  let openCover x := ball x (dynEntourage T V n)
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover openCover fun x _ => ball_mem_nhds x uni_ite
exact ⟨s, .of_entourage

Depends on / 依赖: F_comp, F_comp.elim_nhds_subcover, SetRel, U_uni, ball_mem_nhds, dynEntourage, dynEntourage_mem_uniformity, elim_nhds_subcover, hVsymm, of_entourage_subset, of_subset_iUnion_ball, openCover, s_cover, symm_of_uniformity, uni_ite
-/
lemma exists_isDynCoverOf_of_isCompact_uniformContinuous [UniformSpace X]
    (F_comp : IsCompact F) (h : UniformContinuous T) (U_uni : U in 𝓤 X) (n : Nat) :
    exists s : Finset X, IsDynCoverOf T F U n s := by
  obtain ⟨(V : SetRel X X), hV, hVsymm, hVU⟩ := symm_of_uniformity U_uni
  have uni_ite := dynEntourage_mem_uniformity h hV n
  let openCover x := ball x (dynEntourage T V n)
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover openCover fun x _ => ball_mem_nhds x uni_ite
exact ⟨s, .of_entourage_subset hVU .of_subset_iUnion_ball s_cover⟩

/--
lemma `exists_isDynCoverOf_of_isCompact_invariant` / 引理 `exists_isDynCoverOf_of_isCompact_invariant`

English:
lemma exists_isDynCoverOf_of_isCompact_invariant
  statement: [UniformSpace X]
  proof: by
  obtain ⟨(V : SetRel X X), V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover (ball · V)
    fun (x : X) _ => ball_mem_nhds x V_uni
have : IsDynCoverOf T F V 1 s := .of_subset_iUnion_ball by simpa using s_cover
  obtain ⟨t, t_dyncover

中文:
引理 存在_isDynCoverOf_of_isCompact_invariant
  结论: [一致空间 X]
  证明: by
  obtain ⟨(V : SetRel X X), V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover (ball · V)
    fun (x : X) _ => ball_mem_nhds x V_uni
have : IsDynCoverOf T F V 1 s := .of_subset_iUnion_ball by simpa using s_cover
  obtain ⟨t, t_dyncover

Depends on / 依赖: F_comp, F_comp.elim_nhds_subcover, F_inv, IsDynCoverOf, SetRel, U_uni, V_symm, V_uni, ball_mem_nhds, comp_symm_mem_uniformity_sets, elim_nhds_subcover, iterate_le_pow, of_entourage_subset, of_subset_iUnion_ball, one_mul, s_cover, t_card, t_dyncover, t_dyncover.of_entourage_subset, this.iterate_le_pow
-/
lemma exists_isDynCoverOf_of_isCompact_invariant [UniformSpace X]
    (F_comp : IsCompact F) (F_inv : MapsTo T F F) (U_uni : U in 𝓤 X) (n : Nat) :
    exists s : Finset X, IsDynCoverOf T F U n s := by
  obtain ⟨(V : SetRel X X), V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover (ball · V)
    fun (x : X) _ => ball_mem_nhds x V_uni
have : IsDynCoverOf T F V 1 s := .of_subset_iUnion_ball by simpa using s_cover
  obtain ⟨t, t_dyncover, t_card⟩ := this.iterate_le_pow F_inv n
  rw [one_mul n] at t_dyncover
  exact ⟨t, t_dyncover.of_entourage_subset V_U⟩

/-! ### Minimal cardinality of dynamical covers -/

/--
Definition of `coverMincard` / `coverMincard` 的定义

English:
definition coverMincard
  signature: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
  body: ⨅ (s : Finset X) (_ : IsDynCoverOf T F U n s), (s.card : Nat∞)

中文:
定义 coverMincard
  签名: (T : X -> X) (F : 集合 X) (U : SetRel X X) (n : 自然数)
  定义体: ⨅ (s : Finset X) (_ : IsDynCoverOf T F U n s), (s.card : Nat∞)

Depends on / 依赖: Finset, IsDynCoverOf, s.card
-/
noncomputable def coverMincard (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) : Nat∞ :=
  ⨅ (s : Finset X) (_ : IsDynCoverOf T F U n s), (s.card : Nat∞)

/--
lemma `IsDynCoverOf.coverMincard_le_card` / 引理 `IsDynCoverOf.coverMincard_le_card`

English:
lemma IsDynCoverOf.coverMincard_le_card
  given: {s : Finset X} (h : IsDynCoverOf T F U n s)
  proof: iInf₂_le s h

中文:
引理 IsDynCoverOf.coverMincard_le_card
  条件: {s : 有限集 X} (h : IsDynCoverOf T F U n s)
  证明: iInf₂_le s h
-/
lemma IsDynCoverOf.coverMincard_le_card {s : Finset X} (h : IsDynCoverOf T F U n s) :
    coverMincard T F U n <= s.card :=
  iInf₂_le s h

/--
lemma `coverMincard_monotone_time` / 引理 `coverMincard_monotone_time`

English:
lemma coverMincard_monotone_time
  given: (T : X -> X) (F : Set X) (U : SetRel X X)
  proof: fun _ _ m_n => biInf_mono fun _ h => h.of_le m_n

中文:
引理 coverMincard_monotone_time
  条件: (T : X -> X) (F : 集合 X) (U : SetRel X X)
  证明: fun _ _ m_n => biInf_mono fun _ h => h.of_le m_n

Depends on / 依赖: biInf_mono, h.of_le, of_le
-/
lemma coverMincard_monotone_time (T : X -> X) (F : Set X) (U : SetRel X X) :
    Monotone fun n : Nat => coverMincard T F U n :=
  fun _ _ m_n => biInf_mono fun _ h => h.of_le m_n

/--
lemma `coverMincard_antitone` / 引理 `coverMincard_antitone`

English:
lemma coverMincard_antitone
  given: (T : X -> X) (F : Set X) (n : Nat)
  proof: fun _ _ U_V => biInf_mono fun _ h => h.of_entourage_subset U_V

中文:
引理 coverMincard_antitone
  条件: (T : X -> X) (F : 集合 X) (n : 自然数)
  证明: fun _ _ U_V => biInf_mono fun _ h => h.of_entourage_subset U_V

Depends on / 依赖: biInf_mono, h.of_entourage_subset, of_entourage_subset
-/
lemma coverMincard_antitone (T : X -> X) (F : Set X) (n : Nat) :
    Antitone fun U : SetRel X X => coverMincard T F U n :=
  fun _ _ U_V => biInf_mono fun _ h => h.of_entourage_subset U_V

/--
lemma `coverMincard_finite_iff` / 引理 `coverMincard_finite_iff`

English:
lemma coverMincard_finite_iff
  given: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
  proof: by
  refine ⟨fun h_fin => ?_, fun ⟨s, _, s_coverMincard⟩ => s_coverMincard ▸ WithTop.coe_lt_top s.card⟩
  obtain ⟨k, k_min⟩ := ENat.ne_top_iff_exists.mp h_fin.ne
  rw [← k_min]
  simp only [Nat.cast_inj]
  have : Nonempty {s : Finset X // IsDynCoverOf T F U n s} := by
    by_contra h
    apply ENat.

中文:
引理 coverMincard_finite_iff
  条件: (T : X -> X) (F : 集合 X) (U : SetRel X X) (n : 自然数)
  证明: by
  refine ⟨fun h_fin => ?_, fun ⟨s, _, s_coverMincard⟩ => s_coverMincard ▸ WithTop.coe_lt_top s.card⟩
  obtain ⟨k, k_min⟩ := ENat.ne_top_iff_exists.mp h_fin.ne
  rw [← k_min]
  simp only [Nat.cast_inj]
  have : Nonempty {s : Finset X // IsDynCoverOf T F U n s} := by
    by_contra h
    apply ENat.

Depends on / 依赖: ENat.natCast_ne_top, ENat.ne_top_iff_exists.mp, Finset, IsDynCover, IsDynCoverOf, Nat.cast_inj, Nonempty, WithTop, WithTop.coe_lt_top, cast_inj, ciInf_mem, coe_lt_top, coverMincard, h_fin, h_fin.ne, imp_false, k_min, natCast_ne_top, ne_top_iff_exists, nonempty_subtype
-/
lemma coverMincard_finite_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) :
    coverMincard T F U n < ⊤ ↔
    exists s : Finset X, IsDynCoverOf T F U n s ∧ s.card = coverMincard T F U n := by
  refine ⟨fun h_fin => ?_, fun ⟨s, _, s_coverMincard⟩ => s_coverMincard ▸ WithTop.coe_lt_top s.card⟩
  obtain ⟨k, k_min⟩ := ENat.ne_top_iff_exists.mp h_fin.ne
  rw [← k_min]
  simp only [Nat.cast_inj]
  have : Nonempty {s : Finset X // IsDynCoverOf T F U n s} := by
    by_contra h
    apply ENat.natCast_ne_top k
    rw [k_min]; rw [coverMincard]; rw [iInf₂_eq_top]
    simp only [ENat.natCast_ne_top, imp_false]
    rw [nonempty_subtype]; rw [not_exists] at h
    exact h
  have key := ciInf_mem fun s : {s : Finset X // IsDynCoverOf T F U n s} => (s.val.card : Nat∞)
  rw [coverMincard]; rw [iInf_subtype'] at k_min
  rw [← k_min]; rw [mem_range]; rw [Subtype.exists] at key
  simp only [Nat.cast_inj, exists_prop] at key
  exact key

@[simp]
/--
lemma `coverMincard_empty` / 引理 `coverMincard_empty`

English:
lemma coverMincard_empty
  statement: coverMincard T ∅ U n = 0
  proof: by
  rw [← nonpos_iff_eq_zero]
  exact sInf_le (by simp [IsDynCoverOf])

中文:
引理 coverMincard_empty
  结论: coverMincard T ∅ U n = 0
  证明: by
  rw [← nonpos_iff_eq_zero]
  exact sInf_le (by simp [IsDynCoverOf])

Depends on / 依赖: IsDynCoverOf, nonpos_iff_eq_zero, sInf_le
-/
lemma coverMincard_empty : coverMincard T ∅ U n = 0 := by
  rw [← nonpos_iff_eq_zero]
  exact sInf_le (by simp [IsDynCoverOf])

/--
lemma `coverMincard_eq_zero_iff` / 引理 `coverMincard_eq_zero_iff`

English:
lemma coverMincard_eq_zero_iff
  given: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
  proof: by
  simp [coverMincard, ENat.iInf_eq_zero]

中文:
引理 coverMincard_eq_zero_iff
  条件: (T : X -> X) (F : 集合 X) (U : SetRel X X) (n : 自然数)
  证明: by
  simp [coverMincard, ENat.iInf_eq_zero]

Depends on / 依赖: ENat.iInf_eq_zero, coverMincard, iInf_eq_zero
-/
lemma coverMincard_eq_zero_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) :
    coverMincard T F U n = 0 ↔ F = ∅ := by
  simp [coverMincard, ENat.iInf_eq_zero]

/--
lemma `one_le_coverMincard_iff` / 引理 `one_le_coverMincard_iff`

English:
lemma one_le_coverMincard_iff
  given: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
  proof: by
  rw [Order.one_le_iff_ne_zero]; rw [nonempty_iff_ne_empty]; rw [not_iff_not]
  exact coverMincard_eq_zero_iff T F U n

中文:
引理 one_le_coverMincard_iff
  条件: (T : X -> X) (F : 集合 X) (U : SetRel X X) (n : 自然数)
  证明: by
  rw [Order.one_le_iff_ne_zero]; rw [nonempty_iff_ne_empty]; rw [not_iff_not]
  exact coverMincard_eq_zero_iff T F U n

Depends on / 依赖: Order.one_le_iff_ne_zero, coverMincard_eq_zero_iff, nonempty_iff_ne_empty, not_iff_not, one_le_iff_ne_zero
-/
lemma one_le_coverMincard_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) :
    1 <= coverMincard T F U n ↔ F.Nonempty := by
  rw [Order.one_le_iff_ne_zero]; rw [nonempty_iff_ne_empty]; rw [not_iff_not]
  exact coverMincard_eq_zero_iff T F U n

/--
lemma `coverMincard_zero` / 引理 `coverMincard_zero`

English:
lemma coverMincard_zero
  given: (T : X -> X) (h : F.Nonempty) (U : SetRel X X)
  proof: by
  apply le_antisymm _ ((one_le_coverMincard_iff T F U 0).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_zero T F U (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton]; rw [Nat.cast_one]

中文:
引理 coverMincard_zero
  条件: (T : X -> X) (h : F.非空) (U : SetRel X X)
  证明: by
  apply le_antisymm _ ((one_le_coverMincard_iff T F U 0).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_zero T F U (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton]; rw [Nat.cast_one]

Depends on / 依赖: Finset, Finset.card_singleton, Finset.coe_singleton, Nat.cast_one, card_singleton, cast_one, coe_singleton, coverMincard_le_card, isDynCoverOf_zero, le_antisymm, one_le_coverMincard_iff, singleton_nonempty, this.coverMincard_le_card.trans_eq, trans_eq
-/
lemma coverMincard_zero (T : X -> X) (h : F.Nonempty) (U : SetRel X X) :
    coverMincard T F U 0 = 1 := by
  apply le_antisymm _ ((one_le_coverMincard_iff T F U 0).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_zero T F U (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton]; rw [Nat.cast_one]

/--
lemma `coverMincard_univ` / 引理 `coverMincard_univ`

English:
lemma coverMincard_univ
  given: (T : X -> X) (h : F.Nonempty) (n : Nat)
  statement: coverMincard T F univ n = 1
  proof: by
  apply le_antisymm _ ((one_le_coverMincard_iff T F univ n).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_univ T F n (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton]; rw [Nat.cast_one]

中文:
引理 coverMincard_univ
  条件: (T : X -> X) (h : F.非空) (n : 自然数)
  结论: coverMincard T F univ n = 1
  证明: by
  apply le_antisymm _ ((one_le_coverMincard_iff T F univ n).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_univ T F n (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton]; rw [Nat.cast_one]

Depends on / 依赖: Finset, Finset.card_singleton, Finset.coe_singleton, Nat.cast_one, card_singleton, cast_one, coe_singleton, coverMincard_le_card, isDynCoverOf_univ, le_antisymm, one_le_coverMincard_iff, singleton_nonempty, this.coverMincard_le_card.trans_eq, trans_eq
-/
lemma coverMincard_univ (T : X -> X) (h : F.Nonempty) (n : Nat) : coverMincard T F univ n = 1 := by
  apply le_antisymm _ ((one_le_coverMincard_iff T F univ n).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_univ T F n (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton]; rw [Nat.cast_one]

/--
lemma `coverMincard_mul_le_pow` / 引理 `coverMincard_mul_le_pow`

English:
lemma coverMincard_mul_le_pow
  given: (F_inv : MapsTo T F F) [U.IsSymm] (m n : Nat)
  proof: by
  rcases F.eq_empty_or_nonempty with rfl | F_nonempty
  · simp
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero, coverMincard_zero T F_nonempty (U ○ U), pow_zero]
  rcases eq_top_or_lt_top (coverMincard T F U m) with h | h
  · simp [*]
  · obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_fi

中文:
引理 coverMincard_mul_le_pow
  条件: (F_inv : 映射到 T F F) [U.是Symm] (m n : 自然数)
  证明: by
  rcases F.eq_empty_or_nonempty with rfl | F_nonempty
  · simp
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero, coverMincard_zero T F_nonempty (U ○ U), pow_zero]
  rcases eq_top_or_lt_top (coverMincard T F U m) with h | h
  · simp [*]
  · obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_fi

Depends on / 依赖: F.eq_empty_or_nonempty, F_inv, F_nonempty, WithTop, WithTop.coe_le_coe, coe_le_coe, coverMincard, coverMincard_finite_iff, coverMincard_le_card, coverMincard_zero, eq_empty_or_nonempty, eq_or_ne, eq_top_or_lt_top, iterate_le_pow, mul_zero, pow_zero, s_cover, s_cover.iterate_le_pow, s_coverMincard, t_cover
-/
lemma coverMincard_mul_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (m n : Nat) :
    coverMincard T F (U ○ U) (m * n) <= coverMincard T F U m ^ n := by
  rcases F.eq_empty_or_nonempty with rfl | F_nonempty
  · simp
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero, coverMincard_zero T F_nonempty (U ○ U), pow_zero]
  rcases eq_top_or_lt_top (coverMincard T F U m) with h | h
  · simp [*]
  · obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U m).1 h
    obtain ⟨t, t_cover, t_sn⟩ := s_cover.iterate_le_pow F_inv n
    rw [← s_coverMincard]
    exact t_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 t_sn)

/--
lemma `coverMincard_le_pow` / 引理 `coverMincard_le_pow`

English:
lemma coverMincard_le_pow
  given: (F_inv : MapsTo T F F) [U.IsSymm] (m_pos : 0 < m) (n : Nat)
  proof: (coverMincard_monotone_time T F (U ○ U) (Nat.lt_mul_div_succ n m_pos).le).trans
    (coverMincard_mul_le_pow F_inv m (n / m + 1))

中文:
引理 coverMincard_le_pow
  条件: (F_inv : 映射到 T F F) [U.是Symm] (m_pos : 0 < m) (n : 自然数)
  证明: (coverMincard_monotone_time T F (U ○ U) (Nat.lt_mul_div_succ n m_pos).le).trans
    (coverMincard_mul_le_pow F_inv m (n / m + 1))

Depends on / 依赖: F_inv, Nat.lt_mul_div_succ, coverMincard_monotone_time, coverMincard_mul_le_pow, lt_mul_div_succ, m_pos
-/
lemma coverMincard_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (m_pos : 0 < m) (n : Nat) :
    coverMincard T F (U ○ U) n <= coverMincard T F U m ^ (n / m + 1) :=
  (coverMincard_monotone_time T F (U ○ U) (Nat.lt_mul_div_succ n m_pos).le).trans
    (coverMincard_mul_le_pow F_inv m (n / m + 1))

/--
lemma `coverMincard_finite_of_isCompact_uniformContinuous` / 引理 `coverMincard_finite_of_isCompact_uniformContinuous`

English:
lemma coverMincard_finite_of_isCompact_uniformContinuous
  statement: [UniformSpace X] (F_comp : IsCompact F)
  proof: by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_uniformContinuous F_comp h U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

中文:
引理 coverMincard_finite_of_isCompact_uniformContinuous
  结论: [一致空间 X] (F_comp : 是紧集 F)
  证明: by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_uniformContinuous F_comp h U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

Depends on / 依赖: F_comp, U_uni, WithTop, WithTop.coe_lt_top, coe_lt_top, coverMincard_le_card, exists_isDynCoverOf_of_isCompact_uniformContinuous, s.card, s_cover, s_cover.coverMincard_le_card.trans_lt, trans_lt
-/
lemma coverMincard_finite_of_isCompact_uniformContinuous [UniformSpace X] (F_comp : IsCompact F)
    (h : UniformContinuous T) (U_uni : U in 𝓤 X) (n : Nat) :
    coverMincard T F U n < ⊤ := by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_uniformContinuous F_comp h U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

/--
lemma `coverMincard_finite_of_isCompact_invariant` / 引理 `coverMincard_finite_of_isCompact_invariant`

English:
lemma coverMincard_finite_of_isCompact_invariant
  statement: [UniformSpace X] (F_comp : IsCompact F)
  proof: by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

中文:
引理 coverMincard_finite_of_isCompact_invariant
  结论: [一致空间 X] (F_comp : 是紧集 F)
  证明: by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

Depends on / 依赖: F_comp, F_inv, U_uni, WithTop, WithTop.coe_lt_top, coe_lt_top, coverMincard_le_card, exists_isDynCoverOf_of_isCompact_invariant, s.card, s_cover, s_cover.coverMincard_le_card.trans_lt, trans_lt
-/
lemma coverMincard_finite_of_isCompact_invariant [UniformSpace X] (F_comp : IsCompact F)
    (F_inv : MapsTo T F F) (U_uni : U in 𝓤 X) (n : Nat) :
    coverMincard T F U n < ⊤ := by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

/--
lemma `nonempty_inter_of_coverMincard` / 引理 `nonempty_inter_of_coverMincard`

English:
lemma nonempty_inter_of_coverMincard
  statement: [U.IsSymm] {s : Finset X} (h : IsDynCoverOf T F U n s)
  proof: by
  -- Otherwise, there is a ball which does not intersect `F`. Removing it yields a smaller cover.
  classical
  by_contra! ⟨x, x_s, ball_empt⟩
  have smaller_cover : IsDynCoverOf T F U n (s.erase x) := by
    intro y y_F
    specialize h y_F
    simp only [s.mem_coe] at h
    simp only [s.coe_era

中文:
引理 nonempty_inter_of_coverMincard
  结论: [U.是Symm] {s : 有限集 X} (h : IsDynCoverOf T F U n s)
  证明: by
  -- Otherwise, there is a ball which does not intersect `F`. Removing it yields a smaller cover.
  classical
  by_contra! ⟨x, x_s, ball_empt⟩
  have smaller_cover : IsDynCoverOf T F U n (s.erase x) := by
    intro y y_F
    specialize h y_F
    simp only [s.mem_coe] at h
    simp only [s.coe_era

Depends on / 依赖: IsUnit, IsUnit.liftRight, MonoidHom, MonoidHom.coe_mk, MonoidHom.domRestrict_apply, OneHom, OneHom.coe_mk, Units.liftRight, coe_mk, coe_mul, domRestrict_apply, f.map_units, liftRight, map_mul, map_units, mul_inv_left, mul_left_comm, mul_mul_mul_comm, toMonoidHom_apply
-/
lemma nonempty_inter_of_coverMincard [U.IsSymm] {s : Finset X} (h : IsDynCoverOf T F U n s)
    (h' : #s = coverMincard T F U n) :
    forall x in s, (F inter ball x (dynEntourage T U n)).Nonempty := by
  -- Otherwise, there is a ball which does not intersect `F`. Removing it yields a smaller cover.
  classical
  by_contra! ⟨x, x_s, ball_empt⟩
  have smaller_cover : IsDynCoverOf T F U n (s.erase x) := by
    intro y y_F
    specialize h y_F
    simp only [s.mem_coe] at h
    simp only [s.coe_erase, mem_sdiff, s.mem_coe, mem_singleton_iff]
    obtain ⟨z, z_s, hz⟩ := h
    refine ⟨z, ⟨z_s, fun z_x => notMem_empty y ?_⟩, hz⟩
    rw [← ball_empt]
    rw [z_x] at hz
exact mem_inter y_F (dynEntourage T U n).symm hz
  apply smaller_cover.coverMincard_le_card.not_gt
  rw [← h']
  exact_mod_cast s.card_erase_lt_of_mem x_s

/-! ### Cover entropy of entourages -/

open ENNReal EReal ExpGrowth Filter

/--
Definition of `coverEntropyEntourage` / `coverEntropyEntourage` 的定义

English:
definition coverEntropyEntourage
  signature: (T : X -> X) (F : Set X) (U : SetRel X X)
  body: expGrowthSup fun n : Nat => coverMincard T F U n

中文:
定义 coverEntropyEntourage
  签名: (T : X -> X) (F : 集合 X) (U : SetRel X X)
  定义体: expGrowthSup fun n : Nat => coverMincard T F U n

Depends on / 依赖: coverMincard, expGrowthSup, map_one, mul_one
-/
noncomputable def coverEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X) :=
  expGrowthSup fun n : Nat => coverMincard T F U n

/--
Definition of `coverEntropyInfEntourage` / `coverEntropyInfEntourage` 的定义

English:
definition coverEntropyInfEntourage
  signature: (T : X -> X) (F : Set X) (U : SetRel X X)
  body: expGrowthInf fun n : Nat => coverMincard T F U n

中文:
定义 coverEntropyInfEntourage
  签名: (T : X -> X) (F : 集合 X) (U : SetRel X X)
  定义体: expGrowthInf fun n : Nat => coverMincard T F U n

Depends on / 依赖: coverMincard, expGrowthInf, mul_comm, mul_inv_left, sec_spec
-/
noncomputable def coverEntropyInfEntourage (T : X -> X) (F : Set X) (U : SetRel X X) :=
  expGrowthInf fun n : Nat => coverMincard T F U n

/--
lemma `coverEntropyInfEntourage_antitone` / 引理 `coverEntropyInfEntourage_antitone`

English:
lemma coverEntropyInfEntourage_antitone
  given: (T : X -> X) (F : Set X)
  proof: fun _ _ U_V => expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_antitone T F n U_V)

中文:
引理 coverEntropyInfEntourage_antitone
  条件: (T : X -> X) (F : 集合 X)
  证明: fun _ _ U_V => expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_antitone T F n U_V)

Depends on / 依赖: ENat.toENNReal_mono, _sec, coverMincard_antitone, expGrowthInf_monotone, f.mk, f.sec, toENNReal_mono
-/
lemma coverEntropyInfEntourage_antitone (T : X -> X) (F : Set X) :
    Antitone fun U : SetRel X X => coverEntropyInfEntourage T F U :=
  fun _ _ U_V => expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_antitone T F n U_V)

/--
lemma `coverEntropyEntourage_antitone` / 引理 `coverEntropyEntourage_antitone`

English:
lemma coverEntropyEntourage_antitone
  given: (T : X -> X) (F : Set X)
  proof: fun _ _ U_V => expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_antitone T F n U_V)

中文:
引理 coverEntropyEntourage_antitone
  条件: (T : X -> X) (F : 集合 X)
  证明: fun _ _ U_V => expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_antitone T F n U_V)

Depends on / 依赖: ENat.toENNReal_mono, coverMincard_antitone, expGrowthSup_monotone, mul_assoc, mul_comm, mul_inv_left, toENNReal_mono
-/
lemma coverEntropyEntourage_antitone (T : X -> X) (F : Set X) :
    Antitone fun U : SetRel X X => coverEntropyEntourage T F U :=
  fun _ _ U_V => expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_antitone T F n U_V)

/--
lemma `coverEntropyInfEntourage_le_coverEntropyEntourage` / 引理 `coverEntropyInfEntourage_le_coverEntropyEntourage`

English:
lemma coverEntropyInfEntourage_le_coverEntropyEntourage
  given: (T : X -> X) (F : Set X) (U : SetRel X X)
  proof: expGrowthInf_le_expGrowthSup

@[simp]

中文:
引理 coverEntropyInfEntourage_le_coverEntropyEntourage
  条件: (T : X -> X) (F : 集合 X) (U : SetRel X X)
  证明: expGrowthInf_le_expGrowthSup

@[simp]

Depends on / 依赖: _spec, expGrowthInf_le_expGrowthSup, mul_comm
-/
lemma coverEntropyInfEntourage_le_coverEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X) :
    coverEntropyInfEntourage T F U <= coverEntropyEntourage T F U :=
  expGrowthInf_le_expGrowthSup

@[simp]
/--
lemma `coverEntropyEntourage_empty` / 引理 `coverEntropyEntourage_empty`

English:
lemma coverEntropyEntourage_empty
  statement: coverEntropyEntourage T ∅ U = ⊥
  proof: by
  simp only [coverEntropyEntourage, coverMincard_empty]
  rw [ENat.toENNReal_zero]; rw [← Pi.zero_def]; rw [expGrowthSup_zero]

@[simp]

中文:
引理 coverEntropyEntourage_empty
  结论: coverEntropyEntourage T ∅ U = ⊥
  证明: by
  simp only [coverEntropyEntourage, coverMincard_empty]
  rw [ENat.toENNReal_zero]; rw [← Pi.zero_def]; rw [expGrowthSup_zero]

@[simp]

Depends on / 依赖: ENat.toENNReal_zero, Pi.zero_def, coverEntropyEntourage, coverMincard_empty, expGrowthSup_zero, toENNReal_zero, zero_def
-/
lemma coverEntropyEntourage_empty : coverEntropyEntourage T ∅ U = ⊥ := by
  simp only [coverEntropyEntourage, coverMincard_empty]
  rw [ENat.toENNReal_zero]; rw [← Pi.zero_def]; rw [expGrowthSup_zero]

@[simp]
/--
lemma `coverEntropyInfEntourage_empty` / 引理 `coverEntropyInfEntourage_empty`

English:
lemma coverEntropyInfEntourage_empty
  statement: coverEntropyInfEntourage T ∅ U = ⊥
  proof: eq_bot_mono (coverEntropyInfEntourage_le_coverEntropyEntourage T ∅ U) coverEntropyEntourage_empty

中文:
引理 coverEntropyInfEntourage_empty
  结论: coverEntropyInfEntourage T ∅ U = ⊥
  证明: eq_bot_mono (coverEntropyInfEntourage_le_coverEntropyEntourage T ∅ U) coverEntropyEntourage_empty

Depends on / 依赖: _iff_mul_eq, coverEntropyEntourage_empty, coverEntropyInfEntourage_le_coverEntropyEntourage, eq_bot_mono, eq_comm, eq_mk
-/
lemma coverEntropyInfEntourage_empty : coverEntropyInfEntourage T ∅ U = ⊥ :=
  eq_bot_mono (coverEntropyInfEntourage_le_coverEntropyEntourage T ∅ U) coverEntropyEntourage_empty

/--
lemma `coverEntropyInfEntourage_nonneg` / 引理 `coverEntropyInfEntourage_nonneg`

English:
lemma coverEntropyInfEntourage_nonneg
  given: (T : X -> X) (h : F.Nonempty) (U : SetRel X X)
  proof: by
  apply Monotone.expGrowthInf_nonneg
  · exact fun _ _ m_n => ENat.toENNReal_mono (coverMincard_monotone_time T F U m_n)
  · rw [ne_eq, funext_iff.not, not_forall]
    use 0
    rw [coverMincard_zero T h U]; rw [Pi.zero_apply]; rw [ENat.toENNReal_one]
    exact one_ne_zero

中文:
引理 coverEntropyInfEntourage_nonneg
  条件: (T : X -> X) (h : F.非空) (U : SetRel X X)
  证明: by
  apply Monotone.expGrowthInf_nonneg
  · exact fun _ _ m_n => ENat.toENNReal_mono (coverMincard_monotone_time T F U m_n)
  · rw [ne_eq, funext_iff.not, not_forall]
    use 0
    rw [coverMincard_zero T h U]; rw [Pi.zero_apply]; rw [ENat.toENNReal_one]
    exact one_ne_zero

Depends on / 依赖: ENat.toENNReal_mono, ENat.toENNReal_one, Monotone, Monotone.expGrowthInf_nonneg, Pi.zero_apply, _eq_iff_eq_mul, _spec, coverMincard_monotone_time, coverMincard_zero, expGrowthInf_nonneg, f.map_units, f.mk, funext_iff, funext_iff.not, map_mul, map_units, mul_assoc, mul_comm, mul_inv_right, ne_eq
-/
lemma coverEntropyInfEntourage_nonneg (T : X -> X) (h : F.Nonempty) (U : SetRel X X) :
    0 <= coverEntropyInfEntourage T F U := by
  apply Monotone.expGrowthInf_nonneg
  · exact fun _ _ m_n => ENat.toENNReal_mono (coverMincard_monotone_time T F U m_n)
  · rw [ne_eq, funext_iff.not, not_forall]
    use 0
    rw [coverMincard_zero T h U]; rw [Pi.zero_apply]; rw [ENat.toENNReal_one]
    exact one_ne_zero

/--
lemma `coverEntropyEntourage_nonneg` / 引理 `coverEntropyEntourage_nonneg`

English:
lemma coverEntropyEntourage_nonneg
  given: (T : X -> X) (h : F.Nonempty) (U : SetRel X X)
  proof: (coverEntropyInfEntourage_nonneg T h U).trans
    (coverEntropyInfEntourage_le_coverEntropyEntourage T F U)

中文:
引理 coverEntropyEntourage_nonneg
  条件: (T : X -> X) (h : F.非空) (U : SetRel X X)
  证明: (coverEntropyInfEntourage_nonneg T h U).trans
    (coverEntropyInfEntourage_le_coverEntropyEntourage T F U)

Depends on / 依赖: _eq_iff_eq, coverEntropyInfEntourage_le_coverEntropyEntourage, coverEntropyInfEntourage_nonneg, f.mk, mul_comm
-/
lemma coverEntropyEntourage_nonneg (T : X -> X) (h : F.Nonempty) (U : SetRel X X) :
    0 <= coverEntropyEntourage T F U :=
  (coverEntropyInfEntourage_nonneg T h U).trans
    (coverEntropyInfEntourage_le_coverEntropyEntourage T F U)

/--
lemma `coverEntropyEntourage_univ` / 引理 `coverEntropyEntourage_univ`

English:
lemma coverEntropyEntourage_univ
  given: (T : X -> X) (h : F.Nonempty)
  proof: by
  rw [← expGrowthSup_const one_ne_zero one_ne_top]; rw [coverEntropyEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]

中文:
引理 coverEntropyEntourage_univ
  条件: (T : X -> X) (h : F.非空)
  证明: by
  rw [← expGrowthSup_const one_ne_zero one_ne_top]; rw [coverEntropyEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]

Depends on / 依赖: ENat.toENNReal_one, coverEntropyEntourage, coverMincard_univ, expGrowthSup_const, one_ne_top, one_ne_zero, toENNReal_one
-/
lemma coverEntropyEntourage_univ (T : X -> X) (h : F.Nonempty) :
    coverEntropyEntourage T F univ = 0 := by
  rw [← expGrowthSup_const one_ne_zero one_ne_top]; rw [coverEntropyEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]

/--
lemma `coverEntropyInfEntourage_univ` / 引理 `coverEntropyInfEntourage_univ`

English:
lemma coverEntropyInfEntourage_univ
  given: (T : X -> X) (h : F.Nonempty)
  proof: by
  rw [← expGrowthInf_const one_ne_zero one_ne_top]; rw [coverEntropyInfEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]

中文:
引理 coverEntropyInfEntourage_univ
  条件: (T : X -> X) (h : F.非空)
  证明: by
  rw [← expGrowthInf_const one_ne_zero one_ne_top]; rw [coverEntropyInfEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]

Depends on / 依赖: ENat.toENNReal_one, coverEntropyInfEntourage, coverMincard_univ, expGrowthInf_const, f.eq, g.eq, one_ne_top, one_ne_zero, toENNReal_one
-/
lemma coverEntropyInfEntourage_univ (T : X -> X) (h : F.Nonempty) :
    coverEntropyInfEntourage T F univ = 0 := by
  rw [← expGrowthInf_const one_ne_zero one_ne_top]; rw [coverEntropyInfEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]

/--
lemma `coverEntropyEntourage_le_log_coverMincard_div` / 引理 `coverEntropyEntourage_le_log_coverMincard_div`

English:
lemma coverEntropyEntourage_le_log_coverMincard_div
  statement: (F_inv : MapsTo T F F) [U.IsSymm]
  proof: by
  have cv_mono : Monotone fun m => (coverMincard T F (U ○ U) m).toENNReal :=
    fun _ _ k_m => ENat.toENNReal_mono (coverMincard_monotone_time T F (U ○ U) k_m)
  have h := cv_mono.expGrowthSup_comp_mul n_pos
  rw [mul_comm]; rw [← div_eq_iff (natCast_ne_bot n) (natCast_ne_top n) (Nat.cast_ne_zer

中文:
引理 coverEntropyEntourage_le_log_coverMincard_div
  结论: (F_inv : 映射到 T F F) [U.是Symm]
  证明: by
  have cv_mono : Monotone fun m => (coverMincard T F (U ○ U) m).toENNReal :=
    fun _ _ k_m => ENat.toENNReal_mono (coverMincard_monotone_time T F (U ○ U) k_m)
  have h := cv_mono.expGrowthSup_comp_mul n_pos
  rw [mul_comm]; rw [← div_eq_iff (natCast_ne_bot n) (natCast_ne_top n) (Nat.cast_ne_zer

Depends on / 依赖: ENat.toEN, ENat.toENNReal_mono, ENat.toENNReal_pow, Monotone, Nat.cast_ne_zero, cast_ne_zero, cast_nonneg, coverEntropyEntourage, coverMincard, coverMincard_monotone_time, cv_mono, cv_mono.expGrowthSup_comp_mul, div_eq_iff, expGrowthSup_comp_mul, expGrowthSup_monotone, expGrowthSup_pow, monotone_div_right_of_nonneg, mul_comm, n.cast_nonneg, n_pos
-/
lemma coverEntropyEntourage_le_log_coverMincard_div (F_inv : MapsTo T F F) [U.IsSymm]
    (n_pos : n != 0) :
    coverEntropyEntourage T F (U ○ U) <= log (coverMincard T F U n) / n := by
  have cv_mono : Monotone fun m => (coverMincard T F (U ○ U) m).toENNReal :=
    fun _ _ k_m => ENat.toENNReal_mono (coverMincard_monotone_time T F (U ○ U) k_m)
  have h := cv_mono.expGrowthSup_comp_mul n_pos
  rw [mul_comm]; rw [← div_eq_iff (natCast_ne_bot n) (natCast_ne_top n) (Nat.cast_ne_zero.2 n_pos)] at h
  rw [coverEntropyEntourage]; rw [← h]
  apply monotone_div_right_of_nonneg n.cast_nonneg'
  rw [← expGrowthSup_pow]
  refine expGrowthSup_monotone fun m => ?_
  rw [← ENat.toENNReal_pow]
  exact ENat.toENNReal_mono (coverMincard_mul_le_pow F_inv n m)

/--
lemma `IsDynCoverOf.coverEntropyEntourage_le_log_card_div` / 引理 `IsDynCoverOf.coverEntropyEntourage_le_log_card_div`

English:
lemma IsDynCoverOf.coverEntropyEntourage_le_log_card_div
  statement: (F_inv : MapsTo T F F) [U.IsSymm]
  proof: by
  apply (coverEntropyEntourage_le_log_coverMincard_div F_inv n_pos).trans
  apply monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone _)
  exact_mod_cast coverMincard_le_card h

中文:
引理 IsDynCoverOf.coverEntropyEntourage_le_log_card_div
  结论: (F_inv : 映射到 T F F) [U.是Symm]
  证明: by
  apply (coverEntropyEntourage_le_log_coverMincard_div F_inv n_pos).trans
  apply monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone _)
  exact_mod_cast coverMincard_le_card h

Depends on / 依赖: F_inv, _eq_iff_eq, cast_nonneg, coverEntropyEntourage_le_log_coverMincard_div, coverMincard_le_card, f.mk, log_monotone, monotone_div_right_of_nonneg, n.cast_nonneg, n_pos
-/
lemma IsDynCoverOf.coverEntropyEntourage_le_log_card_div (F_inv : MapsTo T F F) [U.IsSymm]
    (n_pos : n != 0) {s : Finset X} (h : IsDynCoverOf T F U n s) :
    coverEntropyEntourage T F (U ○ U) <= log s.card / n := by
  apply (coverEntropyEntourage_le_log_coverMincard_div F_inv n_pos).trans
  apply monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone _)
  exact_mod_cast coverMincard_le_card h

/--
lemma `coverEntropyEntourage_le_coverEntropyInfEntourage` / 引理 `coverEntropyEntourage_le_coverEntropyInfEntourage`

English:
lemma coverEntropyEntourage_le_coverEntropyInfEntourage
  given: (F_inv : MapsTo T F F) [U.IsSymm]
  proof: by
  refine (le_liminf_of_le) (eventually_atTop.2 ⟨1, fun m m_pos => ?_⟩)
  exact coverEntropyEntourage_le_log_coverMincard_div F_inv (Nat.one_le_iff_ne_zero.1 m_pos)

中文:
引理 coverEntropyEntourage_le_coverEntropyInfEntourage
  条件: (F_inv : 映射到 T F F) [U.是Symm]
  证明: by
  refine (le_liminf_of_le) (eventually_atTop.2 ⟨1, fun m m_pos => ?_⟩)
  exact coverEntropyEntourage_le_log_coverMincard_div F_inv (Nat.one_le_iff_ne_zero.1 m_pos)

Depends on / 依赖: F_inv, Nat.one_le_iff_ne_zero, _eq_of_eq, coverEntropyEntourage_le_log_coverMincard_div, eventually_atTop, f.mk, le_liminf_of_le, m_pos, mul_comm, one_le_iff_ne_zero
-/
lemma coverEntropyEntourage_le_coverEntropyInfEntourage (F_inv : MapsTo T F F) [U.IsSymm] :
    coverEntropyEntourage T F (U ○ U) <= coverEntropyInfEntourage T F U := by
  refine (le_liminf_of_le) (eventually_atTop.2 ⟨1, fun m m_pos => ?_⟩)
  exact coverEntropyEntourage_le_log_coverMincard_div F_inv (Nat.one_le_iff_ne_zero.1 m_pos)

/--
lemma `coverEntropyEntourage_finite_of_isCompact_invariant` / 引理 `coverEntropyEntourage_finite_of_isCompact_invariant`

English:
lemma coverEntropyEntourage_finite_of_isCompact_invariant
  statement: [UniformSpace X]
  proof: by
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv V_uni 1
  apply (coverEntropyEntourage_antitone T F V_U).trans_lt
  apply (s_cover.coverEntropyEntourage_le_log_card_div F_inv one_ne_zero).tran

中文:
引理 coverEntropyEntourage_finite_of_isCompact_invariant
  结论: [一致空间 X]
  证明: by
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv V_uni 1
  apply (coverEntropyEntourage_antitone T F V_U).trans_lt
  apply (s_cover.coverEntropyEntourage_le_log_card_div F_inv one_ne_zero).tran

Depends on / 依赖: ENat.natCast_ne_top, ENat.toENNReal_top, F_comp, F_inv, Finset, Finset.card, Nat.cast_one, Submonoid, Submonoid.coe_mul, U_uni, V_symm, V_uni, _eq_of_eq, cast_one, coe_mul, comp_symm_mem_uniformity_sets, coverEntropyEntourage_antitone, coverEntropyEntourage_le_log_card_div, div_one, exists_isDynCoverOf_of_isCompact_invariant
-/
lemma coverEntropyEntourage_finite_of_isCompact_invariant [UniformSpace X]
    (F_comp : IsCompact F) (F_inv : MapsTo T F F) (U_uni : U in 𝓤 X) :
    coverEntropyEntourage T F U < ⊤ := by
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv V_uni 1
  apply (coverEntropyEntourage_antitone T F V_U).trans_lt
  apply (s_cover.coverEntropyEntourage_le_log_card_div F_inv one_ne_zero).trans_lt
  rw [Nat.cast_one]; rw [div_one]; rw [log_lt_top_iff]; rw [← ENat.toENNReal_top]
  exact_mod_cast (ENat.natCast_ne_top (Finset.card s)).lt_top

/-! ### Cover entropy -/

/--
Definition of `coverEntropy` / `coverEntropy` 的定义

English:
definition coverEntropy
  signature: [UniformSpace X] (T : X -> X) (F : Set X)
  body: ⨆ U in 𝓤 X, coverEntropyEntourage T F U

中文:
定义 coverEntropy
  签名: [一致空间 X] (T : X -> X) (F : 集合 X)
  定义体: ⨆ U in 𝓤 X, coverEntropyEntourage T F U

Depends on / 依赖: _eq_iff_eq, coverEntropyEntourage, eq_iff_exists, map_mul, map_units, mul_left_inj
-/
noncomputable def coverEntropy [UniformSpace X] (T : X -> X) (F : Set X) :=
  ⨆ U in 𝓤 X, coverEntropyEntourage T F U

/--
Definition of `coverEntropyInf` / `coverEntropyInf` 的定义

English:
definition coverEntropyInf
  signature: [UniformSpace X] (T : X -> X) (F : Set X)
  body: ⨆ U in 𝓤 X, coverEntropyInfEntourage T F U

中文:
定义 coverEntropyInf
  签名: [一致空间 X] (T : X -> X) (F : 集合 X)
  定义体: ⨆ U in 𝓤 X, coverEntropyInfEntourage T F U

Depends on / 依赖: coverEntropyInfEntourage, mul_inv_left, mul_one
-/
noncomputable def coverEntropyInf [UniformSpace X] (T : X -> X) (F : Set X) :=
  ⨆ U in 𝓤 X, coverEntropyInfEntourage T F U

/--
lemma `coverEntropyInf_antitone` / 引理 `coverEntropyInf_antitone`

English:
lemma coverEntropyInf_antitone
  given: (T : X -> X) (F : Set X)
  proof: fun _ _ h => iSup₂_mono' fun U U_uni => ⟨U, (le_def.1 h) U U_uni, le_refl _⟩

中文:
引理 coverEntropyInf_antitone
  条件: (T : X -> X) (F : 集合 X)
  证明: fun _ _ h => iSup₂_mono' fun U U_uni => ⟨U, (le_def.1 h) U U_uni, le_refl _⟩

Depends on / 依赖: U_uni, _self, le_def, le_refl
-/
lemma coverEntropyInf_antitone (T : X -> X) (F : Set X) :
    Antitone fun (u : UniformSpace X) => @coverEntropyInf X u T F :=
  fun _ _ h => iSup₂_mono' fun U U_uni => ⟨U, (le_def.1 h) U U_uni, le_refl _⟩

/--
lemma `coverEntropy_antitone` / 引理 `coverEntropy_antitone`

English:
lemma coverEntropy_antitone
  given: (T : X -> X) (F : Set X)
  proof: fun _ _ h => iSup₂_mono' fun U U_uni => ⟨U, (le_def.1 h) U U_uni, le_refl _⟩

中文:
引理 coverEntropy_antitone
  条件: (T : X -> X) (F : 集合 X)
  证明: fun _ _ h => iSup₂_mono' fun U U_uni => ⟨U, (le_def.1 h) U U_uni, le_refl _⟩

Depends on / 依赖: U_uni, le_def, le_refl
-/
lemma coverEntropy_antitone (T : X -> X) (F : Set X) :
    Antitone fun (u : UniformSpace X) => @coverEntropy X u T F :=
  fun _ _ h => iSup₂_mono' fun U U_uni => ⟨U, (le_def.1 h) U U_uni, le_refl _⟩

variable [UniformSpace X]

/--
lemma `coverEntropyEntourage_le_coverEntropy` / 引理 `coverEntropyEntourage_le_coverEntropy`

English:
lemma coverEntropyEntourage_le_coverEntropy
  statement: (T : X -> X) (F : Set X)
  proof: le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => coverEntropyEntourage T F U) U h

中文:
引理 coverEntropyEntourage_le_coverEntropy
  结论: (T : X -> X) (F : 集合 X)
  证明: le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => coverEntropyEntourage T F U) U h

Depends on / 依赖: SetRel, _eq_mk, _of_mul, coverEntropyEntourage, mul_comm, mul_mk
-/
lemma coverEntropyEntourage_le_coverEntropy (T : X -> X) (F : Set X)
    (h : U in 𝓤 X) :
    coverEntropyEntourage T F U <= coverEntropy T F :=
  le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => coverEntropyEntourage T F U) U h

/--
lemma `coverEntropyInfEntourage_le_coverEntropyInf` / 引理 `coverEntropyInfEntourage_le_coverEntropyInf`

English:
lemma coverEntropyInfEntourage_le_coverEntropyInf
  statement: (T : X -> X) (F : Set X)
  proof: le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => coverEntropyInfEntourage T F U) U h

中文:
引理 coverEntropyInfEntourage_le_coverEntropyInf
  结论: (T : X -> X) (F : 集合 X)
  证明: le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => coverEntropyInfEntourage T F U) U h

Depends on / 依赖: SetRel, _eq_mk, _of_mul, coverEntropyInfEntourage, mul_mk, mul_one
-/
lemma coverEntropyInfEntourage_le_coverEntropyInf (T : X -> X) (F : Set X)
    (h : U in 𝓤 X) :
    coverEntropyInfEntourage T F U <= coverEntropyInf T F :=
  le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => coverEntropyInfEntourage T F U) U h

/--
lemma `coverEntropy_eq_iSup_basis` / 引理 `coverEntropy_eq_iSup_basis`

English:
lemma coverEntropy_eq_iSup_basis
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> SetRel X X}
  proof: by
  refine (iSup₂_le fun U U_uni => ?_).antisymm
    (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) => coverEntropyEntour

中文:
引理 coverEntropy_eq_iSup_basis
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> SetRel X X}
  证明: by
  refine (iSup₂_le fun U U_uni => ?_).antisymm
    (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) => coverEntropyEntour

Depends on / 依赖: HasBasis, HasBasis.mem_iff, HasBasis.mem_of_mem, U_uni, _one_eq_mk, _self, antisymm, coverEntropyEntourage, coverEntropyEntourage_antitone, le_refl, map_mul, mem_iff, mem_of_mem, mul_assoc, mul_mk, mul_one, si_U
-/
lemma coverEntropy_eq_iSup_basis {ι : Sort*} {p : ι -> Prop} {s : ι -> SetRel X X}
    (h : (𝓤 X).HasBasis p s) (T : X -> X) (F : Set X) :
    coverEntropy T F = ⨆ (i : ι) (_ : p i), coverEntropyEntourage T F (s i) := by
  refine (iSup₂_le fun U U_uni => ?_).antisymm
    (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) => coverEntropyEntourage T F (s i)) i h_i)

/--
lemma `coverEntropyInf_eq_iSup_basis` / 引理 `coverEntropyInf_eq_iSup_basis`

English:
lemma coverEntropyInf_eq_iSup_basis
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> SetRel X X}
  proof: by
  refine (iSup₂_le fun U U_uni => ?_).antisymm
    (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyInfEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) => coverEntropyInf

中文:
引理 coverEntropyInf_eq_iSup_basis
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> SetRel X X}
  证明: by
  refine (iSup₂_le fun U U_uni => ?_).antisymm
    (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyInfEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) => coverEntropyInf

Depends on / 依赖: HasBasis, HasBasis.mem_iff, HasBasis.mem_of_mem, U_uni, _mul_cancel_right, antisymm, coverEntropyInfEntourage, coverEntropyInfEntourage_antitone, le_refl, mem_iff, mem_of_mem, mul_comm, si_U
-/
lemma coverEntropyInf_eq_iSup_basis {ι : Sort*} {p : ι -> Prop} {s : ι -> SetRel X X}
    (h : (𝓤 X).HasBasis p s) (T : X -> X) (F : Set X) :
    coverEntropyInf T F = ⨆ (i : ι) (_ : p i), coverEntropyInfEntourage T F (s i) := by
  refine (iSup₂_le fun U U_uni => ?_).antisymm
    (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyInfEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) => coverEntropyInfEntourage T F (s i)) i h_i)

/--
lemma `coverEntropyInf_le_coverEntropy` / 引理 `coverEntropyInf_le_coverEntropy`

English:
lemma coverEntropyInf_le_coverEntropy
  given: (T : X -> X) (F : Set X)
  proof: iSup₂_mono fun (U : SetRel X X) (_ : U in 𝓤 X) =>
    coverEntropyInfEntourage_le_coverEntropyEntourage T F U

@[simp]

中文:
引理 coverEntropyInf_le_coverEntropy
  条件: (T : X -> X) (F : 集合 X)
  证明: iSup₂_mono fun (U : SetRel X X) (_ : U in 𝓤 X) =>
    coverEntropyInfEntourage_le_coverEntropyEntourage T F U

@[simp]

Depends on / 依赖: SetRel, coverEntropyInfEntourage_le_coverEntropyEntourage
-/
lemma coverEntropyInf_le_coverEntropy (T : X -> X) (F : Set X) :
    coverEntropyInf T F <= coverEntropy T F :=
  iSup₂_mono fun (U : SetRel X X) (_ : U in 𝓤 X) =>
    coverEntropyInfEntourage_le_coverEntropyEntourage T F U

@[simp]
/--
lemma `coverEntropy_empty` / 引理 `coverEntropy_empty`

English:
lemma coverEntropy_empty
  statement: coverEntropy T ∅ = ⊥
  proof: by
  simp only [coverEntropy, coverEntropyEntourage_empty, iSup_bot]

@[simp]

中文:
引理 coverEntropy_empty
  结论: coverEntropy T ∅ = ⊥
  证明: by
  simp only [coverEntropy, coverEntropyEntourage_empty, iSup_bot]

@[simp]

Depends on / 依赖: coverEntropy, coverEntropyEntourage_empty, iSup_bot
-/
lemma coverEntropy_empty : coverEntropy T ∅ = ⊥ := by
  simp only [coverEntropy, coverEntropyEntourage_empty, iSup_bot]

@[simp]
/--
lemma `coverEntropyInf_empty` / 引理 `coverEntropyInf_empty`

English:
lemma coverEntropyInf_empty
  statement: coverEntropyInf T ∅ = ⊥
  proof: by
  simp only [coverEntropyInf, coverEntropyInfEntourage_empty, iSup_bot]

中文:
引理 coverEntropyInf_empty
  结论: coverEntropyInf T ∅ = ⊥
  证明: by
  simp only [coverEntropyInf, coverEntropyInfEntourage_empty, iSup_bot]

Depends on / 依赖: coverEntropyInf, coverEntropyInfEntourage_empty, iSup_bot
-/
lemma coverEntropyInf_empty : coverEntropyInf T ∅ = ⊥ := by
  simp only [coverEntropyInf, coverEntropyInfEntourage_empty, iSup_bot]

/--
lemma `coverEntropyInf_nonneg` / 引理 `coverEntropyInf_nonneg`

English:
lemma coverEntropyInf_nonneg
  given: (T : X -> X) (h : F.Nonempty)
  statement: 0 <= coverEntropyInf T F
  proof: (coverEntropyInfEntourage_le_coverEntropyInf T F univ_mem).trans_eq'
    (coverEntropyInfEntourage_univ T h)

中文:
引理 coverEntropyInf_nonneg
  条件: (T : X -> X) (h : F.非空)
  结论: 0 <= coverEntropyInf T F
  证明: (coverEntropyInfEntourage_le_coverEntropyInf T F univ_mem).trans_eq'
    (coverEntropyInfEntourage_univ T h)

Depends on / 依赖: coverEntropyInfEntourage_le_coverEntropyInf, coverEntropyInfEntourage_univ, trans_eq, univ_mem
-/
lemma coverEntropyInf_nonneg (T : X -> X) (h : F.Nonempty) : 0 <= coverEntropyInf T F :=
  (coverEntropyInfEntourage_le_coverEntropyInf T F univ_mem).trans_eq'
    (coverEntropyInfEntourage_univ T h)

/--
lemma `coverEntropy_nonneg` / 引理 `coverEntropy_nonneg`

English:
lemma coverEntropy_nonneg
  given: (T : X -> X) (h : F.Nonempty)
  statement: 0 <= coverEntropy T F
  proof: (coverEntropyInf_nonneg T h).trans (coverEntropyInf_le_coverEntropy T F)

中文:
引理 coverEntropy_nonneg
  条件: (T : X -> X) (h : F.非空)
  结论: 0 <= coverEntropy T F
  证明: (coverEntropyInf_nonneg T h).trans (coverEntropyInf_le_coverEntropy T F)

Depends on / 依赖: coverEntropyInf_le_coverEntropy, coverEntropyInf_nonneg
-/
lemma coverEntropy_nonneg (T : X -> X) (h : F.Nonempty) : 0 <= coverEntropy T F :=
  (coverEntropyInf_nonneg T h).trans (coverEntropyInf_le_coverEntropy T F)

/--
lemma `coverEntropyInf_eq_coverEntropy` / 引理 `coverEntropyInf_eq_coverEntropy`

English:
lemma coverEntropyInf_eq_coverEntropy
  given: (T : X -> X) (h : MapsTo T F F)
  proof: by
  refine le_antisymm (coverEntropyInf_le_coverEntropy T F) (iSup₂_le fun U U_uni => ?_)
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
exact (coverEntropyEntourage_antitone T F V_U).trans le_iSup₂_of_le V V_uni
     coverEntropyEntourage_le_coverEntropyInfEntourage h

中文:
引理 coverEntropyInf_eq_coverEntropy
  条件: (T : X -> X) (h : 映射到 T F F)
  证明: by
  refine le_antisymm (coverEntropyInf_le_coverEntropy T F) (iSup₂_le fun U U_uni => ?_)
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
exact (coverEntropyEntourage_antitone T F V_U).trans le_iSup₂_of_le V V_uni
     coverEntropyEntourage_le_coverEntropyInfEntourage h

Depends on / 依赖: U_uni, V_symm, V_uni, _apply, comp_symm_mem_uniformity_sets, coverEntropyEntourage_antitone, coverEntropyEntourage_le_coverEntropyInfEntourage, coverEntropyInf_le_coverEntropy, le_antisymm, mk_eq_monoidOf_mk
-/
lemma coverEntropyInf_eq_coverEntropy (T : X -> X) (h : MapsTo T F F) :
    coverEntropyInf T F = coverEntropy T F := by
  refine le_antisymm (coverEntropyInf_le_coverEntropy T F) (iSup₂_le fun U U_uni => ?_)
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
exact (coverEntropyEntourage_antitone T F V_U).trans le_iSup₂_of_le V V_uni
     coverEntropyEntourage_le_coverEntropyInfEntourage h

end Dynamics
