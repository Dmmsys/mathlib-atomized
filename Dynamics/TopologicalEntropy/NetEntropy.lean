/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy via nets

We implement Bowen-Dinaburg's definitions of the topological entropy, via nets.

The major design decisions are the same as in
`Mathlib/Dynamics/TopologicalEntropy/CoverEntropy.lean`, and are explained in detail there:
use of uniform spaces, definition of the topological entropy of a subset, and values taken in
`EReal`.

Given a map `T : X → X` and a subset `F ⊆ X`, the topological entropy is loosely defined using
nets as the exponential growth (in `n`) of the number of distinguishable orbits of length `n`
starting from `F`. More precisely, given an entourage `U`, two orbits of length `n` can be
distinguished if there exists some index `k < n` such that `T^[k] x` and `T^[k] y` are far enough
(i.e. `(T^[k] x, T^[k] y)` is not in `U`). The maximal number of distinguishable orbits of
length `n` is `netMaxcard T F U n`, and its exponential growth `netEntropyEntourage T F U`. This
quantity increases when `U` decreases, and a definition of the topological entropy is
`⨆ U ∈ 𝓤 X, netEntropyInfEntourage T F U`.

The definition of topological entropy using nets coincides with the definition using covers.
Instead of defining a new notion of topological entropy, we prove that
`coverEntropy` coincides with `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`.

## Main definitions
- `IsDynNetIn`: property that dynamical balls centered on a subset `s` of `F` are disjoint.
- `netMaxcard`: maximal cardinality of a dynamical net. Takes values in `ℕ∞`.
- `netEntropyInfEntourage`/`netEntropyEntourage`: exponential growth of `netMaxcard`. The former is
  defined with a `liminf`, the latter with a `limsup`. Take values in `EReal`.

## Implementation notes
As when using covers, there are two competing definitions `netEntropyInfEntourage` and
`netEntropyEntourage` in this file: one uses a `liminf`, the other a `limsup`. When using covers,
we chose the `limsup` definition as the default.

## Main results
- `coverEntropy_eq_iSup_netEntropyEntourage`: equality between the notions of topological entropy
  defined with covers and with nets. Has a variant for `coverEntropyInf`.

## Tags
net, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

@[expose] public section

open Set Uniformity UniformSpace
open scoped SetRel

namespace Dynamics

variable {X : Type*} {T : X -> X} {U V : SetRel X X} {m n : Nat} {F s : Set X} {x : X}

/-! ### Dynamical nets -/

/--
Definition of `IsDynNetIn` / `IsDynNetIn` 的定义

English:
definition IsDynNetIn
  signature: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) (s : Set X)
  body: s subseteq F ∧ s.PairwiseDisjoint fun x : X => ball x (dynEntourage T U n)

中文:
定义 IsDynNetIn
  签名: (T : X -> X) (F : Set X) (U : SetRel X X) (n : 自然数) (s : Set X)
  定义体: s subseteq F ∧ s.PairwiseDisjoint fun x : X => ball x (dynEntourage T U n)

Depends on / 依赖: PairwiseDisjoint, dynEntourage, s.PairwiseDisjoint, subseteq
-/
def IsDynNetIn (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) (s : Set X) : Prop :=
  s subseteq F ∧ s.PairwiseDisjoint fun x : X => ball x (dynEntourage T U n)

/--
lemma `IsDynNetIn.of_le` / 引理 `IsDynNetIn.of_le`

English:
lemma IsDynNetIn.of_le
  given: (m_n : m <= n) (h : IsDynNetIn T F U m s)
  statement: IsDynNetIn T F U n s
  proof: ⟨h.1, PairwiseDisjoint.mono h.2 fun x => ball_mono (dynEntourage_antitone T U m_n) x⟩

中文:
引理 IsDynNetIn.of_le
  条件: (m_n : m <= n) (h : IsDynNetIn T F U m s)
  结论: IsDynNetIn T F U n s
  证明: ⟨h.1, PairwiseDisjoint.mono h.2 fun x => ball_mono (dynEntourage_antitone T U m_n) x⟩

Depends on / 依赖: PairwiseDisjoint, PairwiseDisjoint.mono, ball_mono, dynEntourage_antitone
-/
lemma IsDynNetIn.of_le (m_n : m <= n) (h : IsDynNetIn T F U m s) : IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 fun x => ball_mono (dynEntourage_antitone T U m_n) x⟩

/--
lemma `IsDynNetIn.of_entourage_subset` / 引理 `IsDynNetIn.of_entourage_subset`

English:
lemma IsDynNetIn.of_entourage_subset
  given: (U_V : U subseteq V) (h : IsDynNetIn T F V n s)
  proof: ⟨h.1, PairwiseDisjoint.mono h.2 fun x => ball_mono (dynEntourage_monotone T n U_V) x⟩

中文:
引理 IsDynNetIn.of_entourage_subset
  条件: (U_V : U subseteq V) (h : IsDynNetIn T F V n s)
  证明: ⟨h.1, PairwiseDisjoint.mono h.2 fun x => ball_mono (dynEntourage_monotone T n U_V) x⟩

Depends on / 依赖: PairwiseDisjoint, PairwiseDisjoint.mono, ball_mono, dynEntourage_monotone
-/
lemma IsDynNetIn.of_entourage_subset (U_V : U subseteq V) (h : IsDynNetIn T F V n s) :
    IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 fun x => ball_mono (dynEntourage_monotone T n U_V) x⟩

/--
lemma `isDynNetIn_empty` / 引理 `isDynNetIn_empty`

English:
lemma isDynNetIn_empty
  statement: IsDynNetIn T F U n ∅
  proof: ⟨empty_subset F, pairwise_empty _⟩

中文:
引理 isDynNetIn_empty
  结论: IsDynNetIn T F U n ∅
  证明: ⟨empty_subset F, pairwise_empty _⟩

Depends on / 依赖: empty_subset, pairwise_empty
-/
lemma isDynNetIn_empty : IsDynNetIn T F U n ∅ := ⟨empty_subset F, pairwise_empty _⟩

/--
lemma `isDynNetIn_singleton` / 引理 `isDynNetIn_singleton`

English:
lemma isDynNetIn_singleton
  given: (T : X -> X) (U : SetRel X X) (n : Nat) (h : x in F)
  proof: ⟨singleton_subset_iff.2 h, pairwise_singleton x _⟩

中文:
引理 isDynNetIn_singleton
  条件: (T : X -> X) (U : SetRel X X) (n : 自然数) (h : x in F)
  证明: ⟨singleton_subset_iff.2 h, pairwise_singleton x _⟩

Depends on / 依赖: pairwise_singleton, singleton_subset_iff
-/
lemma isDynNetIn_singleton (T : X -> X) (U : SetRel X X) (n : Nat) (h : x in F) :
    IsDynNetIn T F U n {x} :=
  ⟨singleton_subset_iff.2 h, pairwise_singleton x _⟩

/--
lemma `IsDynNetIn.card_le_card_of_isDynCoverOf` / 引理 `IsDynNetIn.card_le_card_of_isDynCoverOf`

English:
lemma IsDynNetIn.card_le_card_of_isDynCoverOf
  statement: {s t : Finset X}
  proof: by
  have (x : X) (x_s : x in s) : exists z in t, z in ball x (dynEntourage T U n) := by
    simpa using! ht (hs.1 x_s)
  choose! F s_t using this
  apply Finset.card_le_card_of_injOn F fun x x_s => (s_t x x_s).1
  exact fun x x_s y y_s Fx_Fy =>
    PairwiseDisjoint.elim_set hs.2 x_s y_s (F x) (s_t 

中文:
引理 IsDynNetIn.card_le_card_of_isDynCoverOf
  结论: {s t : Finset X}
  证明: by
  have (x : X) (x_s : x in s) : exists z in t, z in ball x (dynEntourage T U n) := by
    simpa using! ht (hs.1 x_s)
  choose! F s_t using this
  apply Finset.card_le_card_of_injOn F fun x x_s => (s_t x x_s).1
  exact fun x x_s y y_s Fx_Fy =>
    PairwiseDisjoint.elim_set hs.2 x_s y_s (F x) (s_t 

Depends on / 依赖: Finset, Finset.card_le_card_of_injOn, Fx_Fy, PairwiseDisjoint, PairwiseDisjoint.elim_set, card_le_card_of_injOn, dynEntourage, elim_set
-/
lemma IsDynNetIn.card_le_card_of_isDynCoverOf {s t : Finset X}
    (hs : IsDynNetIn T F U n s) (ht : IsDynCoverOf T F U n t) :
    s.card <= t.card := by
  have (x : X) (x_s : x in s) : exists z in t, z in ball x (dynEntourage T U n) := by
    simpa using! ht (hs.1 x_s)
  choose! F s_t using this
  apply Finset.card_le_card_of_injOn F fun x x_s => (s_t x x_s).1
  exact fun x x_s y y_s Fx_Fy =>
    PairwiseDisjoint.elim_set hs.2 x_s y_s (F x) (s_t x x_s).2 (Fx_Fy ▸ (s_t y y_s).2)

/-! ### Maximal cardinality of dynamical nets -/

/--
Definition of `netMaxcard` / `netMaxcard` 的定义

English:
definition netMaxcard
  signature: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
  body: ⨆ (s : Finset X) (_ : IsDynNetIn T F U n s), (s.card : Nat∞)

中文:
定义 netMaxcard
  签名: (T : X -> X) (F : Set X) (U : SetRel X X) (n : 自然数)
  定义体: ⨆ (s : Finset X) (_ : IsDynNetIn T F U n s), (s.card : Nat∞)

Depends on / 依赖: Finset, IsDynNetIn, s.card
-/
noncomputable def netMaxcard (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) : Nat∞ :=
  ⨆ (s : Finset X) (_ : IsDynNetIn T F U n s), (s.card : Nat∞)

/--
lemma `IsDynNetIn.card_le_netMaxcard` / 引理 `IsDynNetIn.card_le_netMaxcard`

English:
lemma IsDynNetIn.card_le_netMaxcard
  given: {s : Finset X} (h : IsDynNetIn T F U n s)
  proof: le_iSup₂ (α := Nat∞) s h

中文:
引理 IsDynNetIn.card_le_netMaxcard
  条件: {s : Finset X} (h : IsDynNetIn T F U n s)
  证明: le_iSup₂ (α := Nat∞) s h
-/
lemma IsDynNetIn.card_le_netMaxcard {s : Finset X} (h : IsDynNetIn T F U n s) :
    s.card <= netMaxcard T F U n :=
  le_iSup₂ (α := Nat∞) s h

/--
lemma `netMaxcard_monotone_time` / 引理 `netMaxcard_monotone_time`

English:
lemma netMaxcard_monotone_time
  given: (T : X -> X) (F : Set X) (U : SetRel X X)
  proof: fun _ _ m_n => biSup_mono fun _ h => h.of_le m_n

中文:
引理 netMaxcard_monotone_time
  条件: (T : X -> X) (F : Set X) (U : SetRel X X)
  证明: fun _ _ m_n => biSup_mono fun _ h => h.of_le m_n

Depends on / 依赖: biSup_mono, h.of_le, of_le
-/
lemma netMaxcard_monotone_time (T : X -> X) (F : Set X) (U : SetRel X X) :
    Monotone fun n : Nat => netMaxcard T F U n :=
  fun _ _ m_n => biSup_mono fun _ h => h.of_le m_n

/--
lemma `netMaxcard_antitone` / 引理 `netMaxcard_antitone`

English:
lemma netMaxcard_antitone
  given: (T : X -> X) (F : Set X) (n : Nat)
  proof: fun _ _ U_V => biSup_mono fun _ h => h.of_entourage_subset U_V

中文:
引理 netMaxcard_antitone
  条件: (T : X -> X) (F : Set X) (n : 自然数)
  证明: fun _ _ U_V => biSup_mono fun _ h => h.of_entourage_subset U_V

Depends on / 依赖: biSup_mono, h.of_entourage_subset, of_entourage_subset
-/
lemma netMaxcard_antitone (T : X -> X) (F : Set X) (n : Nat) :
    Antitone fun U : SetRel X X => netMaxcard T F U n :=
  fun _ _ U_V => biSup_mono fun _ h => h.of_entourage_subset U_V

/--
lemma `netMaxcard_finite_iff` / 引理 `netMaxcard_finite_iff`

English:
lemma netMaxcard_finite_iff
  given: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
  proof: by
  apply Iff.intro <;> intro h
  · obtain ⟨k, k_max⟩ := ENat.ne_top_iff_exists.mp h.ne
    rw [← k_max]
    simp only [Nat.cast_inj]
    -- The criterion we want to use is `Nat.sSup_mem`. We rewrite `netMaxcard` with an `sSup`,
    -- then check its `BddAbove` and `Nonempty` hypotheses.
    have :

中文:
引理 netMaxcard_finite_iff
  条件: (T : X -> X) (F : Set X) (U : SetRel X X) (n : 自然数)
  证明: by
  apply Iff.intro <;> intro h
  · obtain ⟨k, k_max⟩ := ENat.ne_top_iff_exists.mp h.ne
    rw [← k_max]
    simp only [Nat.cast_inj]
    -- The criterion we want to use is `Nat.sSup_mem`. We rewrite `netMaxcard` with an `sSup`,
    -- then check its `BddAbove` and `Nonempty` hypotheses.
    have :

Depends on / 依赖: ENat.ne_top_iff_exists.mp, Iff.intro, Nat.cast_inj, cast_inj, h.ne, k_max, ne_top_iff_exists
-/
lemma netMaxcard_finite_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) :
    netMaxcard T F U n < ⊤ ↔
    exists s : Finset X, IsDynNetIn T F U n s ∧ (s.card : Nat∞) = netMaxcard T F U n := by
  apply Iff.intro <;> intro h
  · obtain ⟨k, k_max⟩ := ENat.ne_top_iff_exists.mp h.ne
    rw [← k_max]
    simp only [Nat.cast_inj]
    -- The criterion we want to use is `Nat.sSup_mem`. We rewrite `netMaxcard` with an `sSup`,
    -- then check its `BddAbove` and `Nonempty` hypotheses.
    have : netMaxcard T F U n
      = sSup (WithTop.some '' Finset.card '' {s : Finset X | IsDynNetIn T F U n s}) := by
      rw [netMaxcard]; rw [← image_comp]; rw [sSup_image]
      simp only [mem_ofPred_eq, ENat.some_eq_natCast, Function.comp_apply]
      exact biSup_congr (fun _ _ => rfl)
    rw [this] at k_max
    have h_bdda : BddAbove (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}) := by
      refine ⟨k, mem_upperBounds.2 ?_⟩
      simp only [mem_image, mem_ofPred_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro s h
      rw [← ENat.natCast_le_natCast]; rw [k_max]
      apply le_sSup
      exact Filter.frequently_principal.mp fun a => a (by simpa using ⟨_, h, rfl⟩) rfl
    have h_nemp : (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}).Nonempty := by
      refine ⟨0, ?_⟩
      simp only [mem_image, mem_ofPred_eq, Finset.card_eq_zero, exists_eq_right, Finset.coe_empty]
      exact isDynNetIn_empty
    rw [← WithTop.coe_sSup' h_bdda] at k_max
    have key := Nat.sSup_mem h_nemp h_bdda
    rw [← Nat.cast_inj.mp k_max]; rw [mem_image] at key
    simp only [mem_ofPred_eq] at key
    exact key
  · obtain ⟨s, _, s_card⟩ := h
    rw [← s_card]
    exact WithTop.coe_lt_top s.card

@[simp]
/--
lemma `netMaxcard_empty` / 引理 `netMaxcard_empty`

English:
lemma netMaxcard_empty
  statement: netMaxcard T ∅ U n = 0
  proof: by
  rw [netMaxcard]; rw [← bot_eq_zero]; rw [iSup₂_eq_bot]
  intro s s_net
  replace s_net := subset_empty_iff.1 s_net.1
  norm_cast at s_net
  rw [s_net]; rw [Finset.card_empty]; rw [CharP.cast_eq_zero]; rw [bot_eq_zero']

中文:
引理 netMaxcard_empty
  结论: netMaxcard T ∅ U n = 0
  证明: by
  rw [netMaxcard]; rw [← bot_eq_zero]; rw [iSup₂_eq_bot]
  intro s s_net
  replace s_net := subset_empty_iff.1 s_net.1
  norm_cast at s_net
  rw [s_net]; rw [Finset.card_empty]; rw [CharP.cast_eq_zero]; rw [bot_eq_zero']

Depends on / 依赖: CharP.cast_eq_zero, Finset, Finset.card_empty, bot_eq_zero, card_empty, cast_eq_zero, netMaxcard, replace, s_net, subset_empty_iff
-/
lemma netMaxcard_empty : netMaxcard T ∅ U n = 0 := by
  rw [netMaxcard]; rw [← bot_eq_zero]; rw [iSup₂_eq_bot]
  intro s s_net
  replace s_net := subset_empty_iff.1 s_net.1
  norm_cast at s_net
  rw [s_net]; rw [Finset.card_empty]; rw [CharP.cast_eq_zero]; rw [bot_eq_zero']

/--
lemma `netMaxcard_eq_zero_iff` / 引理 `netMaxcard_eq_zero_iff`

English:
lemma netMaxcard_eq_zero_iff
  given: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [h, netMaxcard_empty]⟩
  rw [eq_empty_iff_forall_notMem]
  intro x x_F
  have key := isDynNetIn_singleton T U n x_F
  rw [← Finset.coe_singleton] at key
  replace key := key.card_le_netMaxcard
  rw [Finset.card_singleton]; rw [Nat.cast_one]; rw [h] at key
  e

中文:
引理 netMaxcard_eq_zero_iff
  条件: (T : X -> X) (F : Set X) (U : SetRel X X) (n : 自然数)
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [h, netMaxcard_empty]⟩
  rw [eq_empty_iff_forall_notMem]
  intro x x_F
  have key := isDynNetIn_singleton T U n x_F
  rw [← Finset.coe_singleton] at key
  replace key := key.card_le_netMaxcard
  rw [Finset.card_singleton]; rw [Nat.cast_one]; rw [h] at key
  e

Depends on / 依赖: Finset, Finset.card_singleton, Finset.coe_singleton, Nat.cast_one, card_le_netMaxcard, card_singleton, cast_one, coe_singleton, eq_empty_iff_forall_notMem, isDynNetIn_singleton, key.card_le_netMaxcard, key.not_gt, netMaxcard_empty, not_gt, replace, zero_lt_one
-/
lemma netMaxcard_eq_zero_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) :
    netMaxcard T F U n = 0 ↔ F = ∅ := by
  refine ⟨fun h => ?_, fun h => by rw [h, netMaxcard_empty]⟩
  rw [eq_empty_iff_forall_notMem]
  intro x x_F
  have key := isDynNetIn_singleton T U n x_F
  rw [← Finset.coe_singleton] at key
  replace key := key.card_le_netMaxcard
  rw [Finset.card_singleton]; rw [Nat.cast_one]; rw [h] at key
  exact key.not_gt zero_lt_one

/--
lemma `one_le_netMaxcard_iff` / 引理 `one_le_netMaxcard_iff`

English:
lemma one_le_netMaxcard_iff
  given: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
  proof: by
  rw [Order.one_le_iff_ne_zero]; rw [nonempty_iff_ne_empty]
  exact not_iff_not.2 (netMaxcard_eq_zero_iff T F U n)

中文:
引理 one_le_netMaxcard_iff
  条件: (T : X -> X) (F : Set X) (U : SetRel X X) (n : 自然数)
  证明: by
  rw [Order.one_le_iff_ne_zero]; rw [nonempty_iff_ne_empty]
  exact not_iff_not.2 (netMaxcard_eq_zero_iff T F U n)

Depends on / 依赖: Order.one_le_iff_ne_zero, netMaxcard_eq_zero_iff, nonempty_iff_ne_empty, not_iff_not, one_le_iff_ne_zero
-/
lemma one_le_netMaxcard_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) :
    1 <= netMaxcard T F U n ↔ F.Nonempty := by
  rw [Order.one_le_iff_ne_zero]; rw [nonempty_iff_ne_empty]
  exact not_iff_not.2 (netMaxcard_eq_zero_iff T F U n)

/--
lemma `netMaxcard_zero` / 引理 `netMaxcard_zero`

English:
lemma netMaxcard_zero
  given: (T : X -> X) (h : F.Nonempty) (U : SetRel X X)
  statement: netMaxcard T F U 0 = 1
  proof: by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F U 0).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_zero, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 fun x x_s y y_s => ?_
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

中文:
引理 netMaxcard_zero
  条件: (T : X -> X) (h : F.Nonempty) (U : SetRel X X)
  结论: netMaxcard T F U 0 = 1
  证明: by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F U 0).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_zero, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 fun x x_s y y_s => ?_
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

Depends on / 依赖: Finset, Finset.card_le_one, PairwiseDisjoint, PairwiseDisjoint.elim_set, antisymm, card_le_one, dynEntourage_zero, elim_set, f.lift_mk, lift_mk, mem_univ, mul_inv_left, one_le_netMaxcard_iff, preimage_univ, s_net
-/
lemma netMaxcard_zero (T : X -> X) (h : F.Nonempty) (U : SetRel X X) : netMaxcard T F U 0 = 1 := by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F U 0).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_zero, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 fun x x_s y y_s => ?_
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

/--
lemma `netMaxcard_univ` / 引理 `netMaxcard_univ`

English:
lemma netMaxcard_univ
  given: (T : X -> X) (h : F.Nonempty) (n : Nat)
  statement: netMaxcard T F univ n = 1
  proof: by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F univ n).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_univ, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 fun x x_s y y_s => ?_
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

中文:
引理 netMaxcard_univ
  条件: (T : X -> X) (h : F.Nonempty) (n : 自然数)
  结论: netMaxcard T F univ n = 1
  证明: by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F univ n).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_univ, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 fun x x_s y y_s => ?_
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

Depends on / 依赖: Finset, Finset.card_le_one, PairwiseDisjoint, PairwiseDisjoint.elim_set, antisymm, card_le_one, dynEntourage_univ, elim_set, mem_univ, one_le_netMaxcard_iff, preimage_univ, s_net
-/
lemma netMaxcard_univ (T : X -> X) (h : F.Nonempty) (n : Nat) : netMaxcard T F univ n = 1 := by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F univ n).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_univ, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 fun x x_s y y_s => ?_
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

/--
lemma `netMaxcard_infinite_iff` / 引理 `netMaxcard_infinite_iff`

English:
lemma netMaxcard_infinite_iff
  given: (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
  proof: by
  apply Iff.intro <;> intro h
  · intro k
    rw [netMaxcard]; rw [iSup_subtype']; rw [iSup_eq_top] at h
    specialize h k (ENat.natCast_lt_top k)
    simp only [Nat.cast_lt, Subtype.exists, exists_prop] at h
    obtain ⟨s, s_net, s_k⟩ := h
    exact ⟨s, s_net, s_k.le⟩
  · refine ENat.eq_top_iff

中文:
引理 netMaxcard_infinite_iff
  条件: (T : X -> X) (F : Set X) (U : SetRel X X) (n : 自然数)
  证明: by
  apply Iff.intro <;> intro h
  · intro k
    rw [netMaxcard]; rw [iSup_subtype']; rw [iSup_eq_top] at h
    specialize h k (ENat.natCast_lt_top k)
    simp only [Nat.cast_lt, Subtype.exists, exists_prop] at h
    obtain ⟨s, s_net, s_k⟩ := h
    exact ⟨s, s_net, s_k.le⟩
  · refine ENat.eq_top_iff

Depends on / 依赖: ENat.eq_top_iff_forall_gt.mpr, ENat.natCast_lt_top, Iff.intro, Nat.cast_lt, Subtype, Subtype.exists, card_le_netMaxcard, cast_lt, eq_top_iff_forall_gt, exists_prop, iSup_eq_top, iSup_subtype, lt_add_one, natCast_lt_top, netMaxcard, s_card, s_k.le, s_net, s_net.card_le_netMaxcard.trans_lt, specialize
-/
lemma netMaxcard_infinite_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) :
    netMaxcard T F U n = ⊤ ↔ forall k : Nat, exists s : Finset X, IsDynNetIn T F U n s ∧ k <= s.card := by
  apply Iff.intro <;> intro h
  · intro k
    rw [netMaxcard]; rw [iSup_subtype']; rw [iSup_eq_top] at h
    specialize h k (ENat.natCast_lt_top k)
    simp only [Nat.cast_lt, Subtype.exists, exists_prop] at h
    obtain ⟨s, s_net, s_k⟩ := h
    exact ⟨s, s_net, s_k.le⟩
  · refine ENat.eq_top_iff_forall_gt.mpr fun k => ?_
    specialize h (k + 1)
    obtain ⟨s, s_net, s_card⟩ := h
    apply s_net.card_le_netMaxcard.trans_lt'
    rw [Nat.cast_lt]
    exact (lt_add_one k).trans_le s_card

/--
lemma `netMaxcard_le_coverMincard` / 引理 `netMaxcard_le_coverMincard`

English:
lemma netMaxcard_le_coverMincard
  given: (T : X -> X) (F : Set X) (n : Nat)
  proof: by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h | h
  · exact h ▸ le_top
  · obtain ⟨t, t_cover, t_mincard⟩ := (coverMincard_finite_iff T F U n).1 h
    rw [← t_mincard]
    exact iSup₂_le fun s s_net => Nat.cast_le.2 (s_net.card_le_card_of_isDynCoverOf t_cover)

中文:
引理 netMaxcard_le_coverMincard
  条件: (T : X -> X) (F : Set X) (n : 自然数)
  证明: by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h | h
  · exact h ▸ le_top
  · obtain ⟨t, t_cover, t_mincard⟩ := (coverMincard_finite_iff T F U n).1 h
    rw [← t_mincard]
    exact iSup₂_le fun s s_net => Nat.cast_le.2 (s_net.card_le_card_of_isDynCoverOf t_cover)

Depends on / 依赖: Nat.cast_le, card_le_card_of_isDynCoverOf, cast_le, coverMincard, coverMincard_finite_iff, eq_top_or_lt_top, le_top, s_net, s_net.card_le_card_of_isDynCoverOf, t_cover, t_mincard
-/
lemma netMaxcard_le_coverMincard (T : X -> X) (F : Set X) (n : Nat) :
    netMaxcard T F U n <= coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h | h
  · exact h ▸ le_top
  · obtain ⟨t, t_cover, t_mincard⟩ := (coverMincard_finite_iff T F U n).1 h
    rw [← t_mincard]
    exact iSup₂_le fun s s_net => Nat.cast_le.2 (s_net.card_le_card_of_isDynCoverOf t_cover)

/--
lemma `coverMincard_le_netMaxcard` / 引理 `coverMincard_le_netMaxcard`

English:
lemma coverMincard_le_netMaxcard
  given: (T : X -> X) (F : Set X) [U.IsRefl] [U.IsSymm] (n : Nat)
  proof: by
  classical
  -- WLOG, there exists a maximal dynamical net `s`.
  rcases eq_top_or_lt_top (netMaxcard T F U n) with h | h
  · exact h ▸ le_top
  obtain ⟨s, s_net, s_card⟩ := (netMaxcard_finite_iff T F U n).1 h
  rw [← s_card]
  apply IsDynCoverOf.coverMincard_le_card
  -- We have to check that `

中文:
引理 coverMincard_le_netMaxcard
  条件: (T : X -> X) (F : Set X) [U.IsRefl] [U.IsSymm] (n : 自然数)
  证明: by
  classical
  -- WLOG, there exists a maximal dynamical net `s`.
  rcases eq_top_or_lt_top (netMaxcard T F U n) with h | h
  · exact h ▸ le_top
  obtain ⟨s, s_net, s_card⟩ := (netMaxcard_finite_iff T F U n).1 h
  rw [← s_card]
  apply IsDynCoverOf.coverMincard_le_card
  -- We have to check that `

Depends on / 依赖: classical
-/
lemma coverMincard_le_netMaxcard (T : X -> X) (F : Set X) [U.IsRefl] [U.IsSymm] (n : Nat) :
    coverMincard T F (U ○ U) n <= netMaxcard T F U n := by
  classical
  -- WLOG, there exists a maximal dynamical net `s`.
  rcases eq_top_or_lt_top (netMaxcard T F U n) with h | h
  · exact h ▸ le_top
  obtain ⟨s, s_net, s_card⟩ := (netMaxcard_finite_iff T F U n).1 h
  rw [← s_card]
  apply IsDynCoverOf.coverMincard_le_card
  -- We have to check that `s` is a cover for `dynEntourage T F (U ○ U) n`.
  -- If `s` is not a cover, then we can add to `s` a point `x` which is not covered
  -- and get a new net. This contradicts the maximality of `s`.
  rw [IsDynCoverOf]; rw [isCover_iff_subset_iUnion_ball]
  by_contra h
  obtain ⟨x, x_F, x_uncov⟩ := not_subset.1 h
  simp only [Finset.mem_coe, mem_iUnion, exists_prop, not_exists, not_and] at x_uncov
  have larger_net : IsDynNetIn T F U n (insert x s) := by
    refine ⟨insert_subset x_F s_net.1, pairwiseDisjoint_insert.2 ⟨s_net.2, ?_⟩⟩
    refine fun y y_s _ => disjoint_left.2 fun z z_x z_y => x_uncov y y_s ?_
    exact mem_ball_dynEntourage_comp T n x y (nonempty_of_mem ⟨z_x, z_y⟩)
  rw [← s.coe_insert x] at larger_net
  apply larger_net.card_le_netMaxcard.not_gt
  rw [← s_card]; rw [Nat.cast_lt]
  refine (lt_add_one s.card).trans_eq (s.card_insert_of_notMem fun x_s => ?_).symm
  exact x_uncov x x_s (ball_mono (dynEntourage_monotone T n SetRel.left_subset_comp) x <|
    SetRel.rfl (dynEntourage T U n))

/-! ### Net entropy of entourages -/

open ENNReal EReal ExpGrowth Filter

/--
Definition of `netEntropyEntourage` / `netEntropyEntourage` 的定义

English:
definition netEntropyEntourage
  signature: (T : X -> X) (F : Set X) (U : SetRel X X)
  body: expGrowthSup fun n : Nat => netMaxcard T F U n

中文:
定义 netEntropyEntourage
  签名: (T : X -> X) (F : Set X) (U : SetRel X X)
  定义体: expGrowthSup fun n : Nat => netMaxcard T F U n

Depends on / 依赖: expGrowthSup, netMaxcard
-/
noncomputable def netEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X) :=
  expGrowthSup fun n : Nat => netMaxcard T F U n

/--
Definition of `netEntropyInfEntourage` / `netEntropyInfEntourage` 的定义

English:
definition netEntropyInfEntourage
  signature: (T : X -> X) (F : Set X) (U : SetRel X X)
  body: expGrowthInf fun n : Nat => netMaxcard T F U n

中文:
定义 netEntropyInfEntourage
  签名: (T : X -> X) (F : Set X) (U : SetRel X X)
  定义体: expGrowthInf fun n : Nat => netMaxcard T F U n

Depends on / 依赖: expGrowthInf, netMaxcard
-/
noncomputable def netEntropyInfEntourage (T : X -> X) (F : Set X) (U : SetRel X X) :=
  expGrowthInf fun n : Nat => netMaxcard T F U n

/--
lemma `netEntropyInfEntourage_antitone` / 引理 `netEntropyInfEntourage_antitone`

English:
lemma netEntropyInfEntourage_antitone
  given: (T : X -> X) (F : Set X)
  proof: fun _ _ U_V => expGrowthInf_monotone fun n => ENat.toENNReal_mono (netMaxcard_antitone T F n U_V)

中文:
引理 netEntropyInfEntourage_antitone
  条件: (T : X -> X) (F : Set X)
  证明: fun _ _ U_V => expGrowthInf_monotone fun n => ENat.toENNReal_mono (netMaxcard_antitone T F n U_V)

Depends on / 依赖: ENat.toENNReal_mono, expGrowthInf_monotone, netMaxcard_antitone, toENNReal_mono
-/
lemma netEntropyInfEntourage_antitone (T : X -> X) (F : Set X) :
    Antitone fun U : SetRel X X => netEntropyInfEntourage T F U :=
  fun _ _ U_V => expGrowthInf_monotone fun n => ENat.toENNReal_mono (netMaxcard_antitone T F n U_V)

/--
lemma `netEntropyEntourage_antitone` / 引理 `netEntropyEntourage_antitone`

English:
lemma netEntropyEntourage_antitone
  given: (T : X -> X) (F : Set X)
  proof: fun _ _ U_V => expGrowthSup_monotone fun n => ENat.toENNReal_mono (netMaxcard_antitone T F n U_V)

中文:
引理 netEntropyEntourage_antitone
  条件: (T : X -> X) (F : Set X)
  证明: fun _ _ U_V => expGrowthSup_monotone fun n => ENat.toENNReal_mono (netMaxcard_antitone T F n U_V)

Depends on / 依赖: ENat.toENNReal_mono, expGrowthSup_monotone, netMaxcard_antitone, toENNReal_mono
-/
lemma netEntropyEntourage_antitone (T : X -> X) (F : Set X) :
    Antitone fun U : SetRel X X => netEntropyEntourage T F U :=
  fun _ _ U_V => expGrowthSup_monotone fun n => ENat.toENNReal_mono (netMaxcard_antitone T F n U_V)

/--
lemma `netEntropyInfEntourage_le_netEntropyEntourage` / 引理 `netEntropyInfEntourage_le_netEntropyEntourage`

English:
lemma netEntropyInfEntourage_le_netEntropyEntourage
  given: (T : X -> X) (F : Set X) (U : SetRel X X)
  proof: expGrowthInf_le_expGrowthSup

@[simp]

中文:
引理 netEntropyInfEntourage_le_netEntropyEntourage
  条件: (T : X -> X) (F : Set X) (U : SetRel X X)
  证明: expGrowthInf_le_expGrowthSup

@[simp]

Depends on / 依赖: expGrowthInf_le_expGrowthSup
-/
lemma netEntropyInfEntourage_le_netEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X) :
    netEntropyInfEntourage T F U <= netEntropyEntourage T F U :=
  expGrowthInf_le_expGrowthSup

@[simp]
/--
lemma `netEntropyEntourage_empty` / 引理 `netEntropyEntourage_empty`

English:
lemma netEntropyEntourage_empty
  statement: netEntropyEntourage T ∅ U = ⊥
  proof: by
  rw [netEntropyEntourage]; rw [← expGrowthSup_zero]
  congr
  simp only [netMaxcard_empty, ENat.toENNReal_zero, Pi.zero_def]

@[simp]

中文:
引理 netEntropyEntourage_empty
  结论: netEntropyEntourage T ∅ U = ⊥
  证明: by
  rw [netEntropyEntourage]; rw [← expGrowthSup_zero]
  congr
  simp only [netMaxcard_empty, ENat.toENNReal_zero, Pi.zero_def]

@[simp]

Depends on / 依赖: ENat.toENNReal_zero, Pi.zero_def, expGrowthSup_zero, netEntropyEntourage, netMaxcard_empty, toENNReal_zero, zero_def
-/
lemma netEntropyEntourage_empty : netEntropyEntourage T ∅ U = ⊥ := by
  rw [netEntropyEntourage]; rw [← expGrowthSup_zero]
  congr
  simp only [netMaxcard_empty, ENat.toENNReal_zero, Pi.zero_def]

@[simp]
/--
lemma `netEntropyInfEntourage_empty` / 引理 `netEntropyInfEntourage_empty`

English:
lemma netEntropyInfEntourage_empty
  statement: netEntropyInfEntourage T ∅ U = ⊥
  proof: eq_bot_mono (netEntropyInfEntourage_le_netEntropyEntourage T ∅ U) netEntropyEntourage_empty

中文:
引理 netEntropyInfEntourage_empty
  结论: netEntropyInfEntourage T ∅ U = ⊥
  证明: eq_bot_mono (netEntropyInfEntourage_le_netEntropyEntourage T ∅ U) netEntropyEntourage_empty

Depends on / 依赖: eq_bot_mono, netEntropyEntourage_empty, netEntropyInfEntourage_le_netEntropyEntourage
-/
lemma netEntropyInfEntourage_empty : netEntropyInfEntourage T ∅ U = ⊥ :=
  eq_bot_mono (netEntropyInfEntourage_le_netEntropyEntourage T ∅ U) netEntropyEntourage_empty

/--
lemma `netEntropyInfEntourage_nonneg` / 引理 `netEntropyInfEntourage_nonneg`

English:
lemma netEntropyInfEntourage_nonneg
  given: (T : X -> X) (h : F.Nonempty) (U : SetRel X X)
  proof: by
  apply Monotone.expGrowthInf_nonneg
  · exact fun _ _ m_n => ENat.toENNReal_mono (netMaxcard_monotone_time T F U m_n)
  · rw [ne_eq, funext_iff.not, not_forall]
    use 0
    rw [netMaxcard_zero T h U]; rw [Pi.zero_apply]; rw [ENat.toENNReal_one]
    exact one_ne_zero

中文:
引理 netEntropyInfEntourage_nonneg
  条件: (T : X -> X) (h : F.Nonempty) (U : SetRel X X)
  证明: by
  apply Monotone.expGrowthInf_nonneg
  · exact fun _ _ m_n => ENat.toENNReal_mono (netMaxcard_monotone_time T F U m_n)
  · rw [ne_eq, funext_iff.not, not_forall]
    use 0
    rw [netMaxcard_zero T h U]; rw [Pi.zero_apply]; rw [ENat.toENNReal_one]
    exact one_ne_zero

Depends on / 依赖: ENat.toENNReal_mono, ENat.toENNReal_one, Monotone, Monotone.expGrowthInf_nonneg, Pi.zero_apply, expGrowthInf_nonneg, funext_iff, funext_iff.not, ne_eq, netMaxcard_monotone_time, netMaxcard_zero, not_forall, one_ne_zero, toENNReal_mono, toENNReal_one, zero_apply
-/
lemma netEntropyInfEntourage_nonneg (T : X -> X) (h : F.Nonempty) (U : SetRel X X) :
    0 <= netEntropyInfEntourage T F U := by
  apply Monotone.expGrowthInf_nonneg
  · exact fun _ _ m_n => ENat.toENNReal_mono (netMaxcard_monotone_time T F U m_n)
  · rw [ne_eq, funext_iff.not, not_forall]
    use 0
    rw [netMaxcard_zero T h U]; rw [Pi.zero_apply]; rw [ENat.toENNReal_one]
    exact one_ne_zero

/--
lemma `netEntropyEntourage_nonneg` / 引理 `netEntropyEntourage_nonneg`

English:
lemma netEntropyEntourage_nonneg
  given: (T : X -> X) (h : F.Nonempty) (U : SetRel X X)
  proof: (netEntropyInfEntourage_nonneg T h U).trans (netEntropyInfEntourage_le_netEntropyEntourage T F U)

中文:
引理 netEntropyEntourage_nonneg
  条件: (T : X -> X) (h : F.Nonempty) (U : SetRel X X)
  证明: (netEntropyInfEntourage_nonneg T h U).trans (netEntropyInfEntourage_le_netEntropyEntourage T F U)

Depends on / 依赖: netEntropyInfEntourage_le_netEntropyEntourage, netEntropyInfEntourage_nonneg
-/
lemma netEntropyEntourage_nonneg (T : X -> X) (h : F.Nonempty) (U : SetRel X X) :
    0 <= netEntropyEntourage T F U :=
  (netEntropyInfEntourage_nonneg T h U).trans (netEntropyInfEntourage_le_netEntropyEntourage T F U)

/--
lemma `netEntropyInfEntourage_univ` / 引理 `netEntropyInfEntourage_univ`

English:
lemma netEntropyInfEntourage_univ
  given: (T : X -> X) {F : Set X} (h : F.Nonempty)
  proof: by
  rw [← expGrowthInf_const one_ne_zero one_ne_top]; rw [netEntropyInfEntourage]
  simp only [netMaxcard_univ T h, ENat.toENNReal_one]

中文:
引理 netEntropyInfEntourage_univ
  条件: (T : X -> X) {F : Set X} (h : F.Nonempty)
  证明: by
  rw [← expGrowthInf_const one_ne_zero one_ne_top]; rw [netEntropyInfEntourage]
  simp only [netMaxcard_univ T h, ENat.toENNReal_one]

Depends on / 依赖: ENat.toENNReal_one, expGrowthInf_const, netEntropyInfEntourage, netMaxcard_univ, one_ne_top, one_ne_zero, toENNReal_one
-/
lemma netEntropyInfEntourage_univ (T : X -> X) {F : Set X} (h : F.Nonempty) :
    netEntropyInfEntourage T F univ = 0 := by
  rw [← expGrowthInf_const one_ne_zero one_ne_top]; rw [netEntropyInfEntourage]
  simp only [netMaxcard_univ T h, ENat.toENNReal_one]

/--
lemma `netEntropyEntourage_univ` / 引理 `netEntropyEntourage_univ`

English:
lemma netEntropyEntourage_univ
  given: (T : X -> X) {F : Set X} (h : F.Nonempty)
  proof: by
  rw [← expGrowthSup_const one_ne_zero one_ne_top]; rw [netEntropyEntourage]
  simp only [netMaxcard_univ T h, ENat.toENNReal_one]

中文:
引理 netEntropyEntourage_univ
  条件: (T : X -> X) {F : Set X} (h : F.Nonempty)
  证明: by
  rw [← expGrowthSup_const one_ne_zero one_ne_top]; rw [netEntropyEntourage]
  simp only [netMaxcard_univ T h, ENat.toENNReal_one]

Depends on / 依赖: ENat.toENNReal_one, expGrowthSup_const, netEntropyEntourage, netMaxcard_univ, one_ne_top, one_ne_zero, toENNReal_one
-/
lemma netEntropyEntourage_univ (T : X -> X) {F : Set X} (h : F.Nonempty) :
    netEntropyEntourage T F univ = 0 := by
  rw [← expGrowthSup_const one_ne_zero one_ne_top]; rw [netEntropyEntourage]
  simp only [netMaxcard_univ T h, ENat.toENNReal_one]

/--
lemma `netEntropyInfEntourage_le_coverEntropyInfEntourage` / 引理 `netEntropyInfEntourage_le_coverEntropyInfEntourage`

English:
lemma netEntropyInfEntourage_le_coverEntropyInfEntourage
  given: (T : X -> X) (F : Set X)
  proof: expGrowthInf_monotone fun n => ENat.toENNReal_mono (netMaxcard_le_coverMincard T F n)

中文:
引理 netEntropyInfEntourage_le_coverEntropyInfEntourage
  条件: (T : X -> X) (F : Set X)
  证明: expGrowthInf_monotone fun n => ENat.toENNReal_mono (netMaxcard_le_coverMincard T F n)

Depends on / 依赖: ENat.toENNReal_mono, expGrowthInf_monotone, netMaxcard_le_coverMincard, toENNReal_mono
-/
lemma netEntropyInfEntourage_le_coverEntropyInfEntourage (T : X -> X) (F : Set X) :
    netEntropyInfEntourage T F U <= coverEntropyInfEntourage T F U :=
  expGrowthInf_monotone fun n => ENat.toENNReal_mono (netMaxcard_le_coverMincard T F n)

/--
lemma `coverEntropyInfEntourage_le_netEntropyInfEntourage` / 引理 `coverEntropyInfEntourage_le_netEntropyInfEntourage`

English:
lemma coverEntropyInfEntourage_le_netEntropyInfEntourage
  statement: (T : X -> X) (F : Set X) [U.IsRefl]
  proof: expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_le_netMaxcard T F n)

中文:
引理 coverEntropyInfEntourage_le_netEntropyInfEntourage
  结论: (T : X -> X) (F : Set X) [U.IsRefl]
  证明: expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_le_netMaxcard T F n)

Depends on / 依赖: ENat.toENNReal_mono, coverMincard_le_netMaxcard, expGrowthInf_monotone, toENNReal_mono
-/
lemma coverEntropyInfEntourage_le_netEntropyInfEntourage (T : X -> X) (F : Set X) [U.IsRefl]
    [U.IsSymm] :
    coverEntropyInfEntourage T F (U ○ U) <= netEntropyInfEntourage T F U :=
  expGrowthInf_monotone fun n => ENat.toENNReal_mono (coverMincard_le_netMaxcard T F n)

/--
lemma `netEntropyEntourage_le_coverEntropyEntourage` / 引理 `netEntropyEntourage_le_coverEntropyEntourage`

English:
lemma netEntropyEntourage_le_coverEntropyEntourage
  given: (T : X -> X) (F : Set X)
  proof: expGrowthSup_monotone fun n => ENat.toENNReal_mono (netMaxcard_le_coverMincard T F n)

中文:
引理 netEntropyEntourage_le_coverEntropyEntourage
  条件: (T : X -> X) (F : Set X)
  证明: expGrowthSup_monotone fun n => ENat.toENNReal_mono (netMaxcard_le_coverMincard T F n)

Depends on / 依赖: ENat.toENNReal_mono, expGrowthSup_monotone, netMaxcard_le_coverMincard, toENNReal_mono
-/
lemma netEntropyEntourage_le_coverEntropyEntourage (T : X -> X) (F : Set X) :
    netEntropyEntourage T F U <= coverEntropyEntourage T F U :=
  expGrowthSup_monotone fun n => ENat.toENNReal_mono (netMaxcard_le_coverMincard T F n)

/--
lemma `coverEntropyEntourage_le_netEntropyEntourage` / 引理 `coverEntropyEntourage_le_netEntropyEntourage`

English:
lemma coverEntropyEntourage_le_netEntropyEntourage
  given: (T : X -> X) (F : Set X) [U.IsRefl] [U.IsSymm]
  proof: expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_le_netMaxcard T F n)

中文:
引理 coverEntropyEntourage_le_netEntropyEntourage
  条件: (T : X -> X) (F : Set X) [U.IsRefl] [U.IsSymm]
  证明: expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_le_netMaxcard T F n)

Depends on / 依赖: ENat.toENNReal_mono, coverMincard_le_netMaxcard, expGrowthSup_monotone, toENNReal_mono
-/
lemma coverEntropyEntourage_le_netEntropyEntourage (T : X -> X) (F : Set X) [U.IsRefl] [U.IsSymm] :
    coverEntropyEntourage T F (U ○ U) <= netEntropyEntourage T F U :=
  expGrowthSup_monotone fun n => ENat.toENNReal_mono (coverMincard_le_netMaxcard T F n)

/-! ### Relationship with entropy via covers -/

variable [UniformSpace X] (T : X -> X) (F : Set X)

/--
theorem `coverEntropyInf_eq_iSup_netEntropyInfEntourage` / 定理 `coverEntropyInf_eq_iSup_netEntropyInfEntourage`

English:
theorem coverEntropyInf_eq_iSup_netEntropyInfEntourage
  proof: by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni => ?_
  · obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
    have := isRefl_of_mem_uniformity V_uni
    apply (coverEntropyInfEntourage_antitone T F V_U).trans (le_iSup₂_of_le V V_uni _)
    exact coverEntropyInfEntourage_

中文:
定理 coverEntropyInf_eq_iSup_netEntropyInfEntourage
  证明: by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni => ?_
  · obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
    have := isRefl_of_mem_uniformity V_uni
    apply (coverEntropyInfEntourage_antitone T F V_U).trans (le_iSup₂_of_le V V_uni _)
    exact coverEntropyInfEntourage_

Depends on / 依赖: SetRel, SetRel.symmetrize, SetRel.symmetrize_subset_self, U_uni, V_symm, V_uni, comp_symm_mem_uniformity_sets, coverEntropyInfEntourage_antitone, coverEntropyInfEntourage_le_netEntropyInfEntourage, isRefl_of_mem_uniformity, le_antisymm, netEntropyInfEntou, netEntropyInfEntourage_antitone, symmetrize, symmetrize_mem_uniformity, symmetrize_subset_self
-/
theorem coverEntropyInf_eq_iSup_netEntropyInfEntourage :
    coverEntropyInf T F = ⨆ U in 𝓤 X, netEntropyInfEntourage T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni => ?_
  · obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
    have := isRefl_of_mem_uniformity V_uni
    apply (coverEntropyInfEntourage_antitone T F V_U).trans (le_iSup₂_of_le V V_uni _)
    exact coverEntropyInfEntourage_le_netEntropyInfEntourage T F
  · apply (netEntropyInfEntourage_antitone T F SetRel.symmetrize_subset_self).trans
    apply (le_iSup₂ (SetRel.symmetrize U) (symmetrize_mem_uniformity U_uni)).trans'
    exact netEntropyInfEntourage_le_coverEntropyInfEntourage T F

/--
theorem `coverEntropy_eq_iSup_netEntropyEntourage` / 定理 `coverEntropy_eq_iSup_netEntropyEntourage`

English:
theorem coverEntropy_eq_iSup_netEntropyEntourage
  proof: by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni => ?_
  · obtain ⟨V, V_uni, V_symm, V_comp_U⟩ := comp_symm_mem_uniformity_sets U_uni
    apply (coverEntropyEntourage_antitone T F V_comp_U).trans (le_iSup₂_of_le V V_uni _)
    have := isRefl_of_mem_uniformity V_uni
    exact coverEntropyEntour

中文:
定理 coverEntropy_eq_iSup_netEntropyEntourage
  证明: by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni => ?_
  · obtain ⟨V, V_uni, V_symm, V_comp_U⟩ := comp_symm_mem_uniformity_sets U_uni
    apply (coverEntropyEntourage_antitone T F V_comp_U).trans (le_iSup₂_of_le V V_uni _)
    have := isRefl_of_mem_uniformity V_uni
    exact coverEntropyEntour

Depends on / 依赖: SetRel, SetRel.symmetrize, SetRel.symmetrize_subset_self, U_uni, V_comp_U, V_symm, V_uni, comp_symm_mem_uniformity_sets, coverEntropyEntourage_antitone, coverEntropyEntourage_le_netEntropyEntourage, isRefl_of_mem_uniformity, le_antisymm, netEntropyEntourage_, netEntropyEntourage_antitone, symmetrize, symmetrize_mem_uniformity, symmetrize_subset_self
-/
theorem coverEntropy_eq_iSup_netEntropyEntourage :
    coverEntropy T F = ⨆ U in 𝓤 X, netEntropyEntourage T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni => ?_
  · obtain ⟨V, V_uni, V_symm, V_comp_U⟩ := comp_symm_mem_uniformity_sets U_uni
    apply (coverEntropyEntourage_antitone T F V_comp_U).trans (le_iSup₂_of_le V V_uni _)
    have := isRefl_of_mem_uniformity V_uni
    exact coverEntropyEntourage_le_netEntropyEntourage T F
  · apply (netEntropyEntourage_antitone T F SetRel.symmetrize_subset_self).trans
    apply (le_iSup₂ (SetRel.symmetrize U) (symmetrize_mem_uniformity U_uni)).trans'
    exact netEntropyEntourage_le_coverEntropyEntourage T F

/--
lemma `coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage` / 引理 `coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage`

English:
lemma coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage
  statement: {ι : Sort*} {p : ι -> Prop}
  proof: by
  rw [coverEntropyInf_eq_iSup_netEntropyInfEntourage T F]
  apply (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni => ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (netEntropyInfEntourage_antitone T F si_U).trans
 

中文:
引理 coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage
  结论: {ι : Sort*} {p : ι -> 命题}
  证明: by
  rw [coverEntropyInf_eq_iSup_netEntropyInfEntourage T F]
  apply (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni => ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (netEntropyInfEntourage_antitone T F si_U).trans
 

Depends on / 依赖: HasBasis, HasBasis.mem_iff, HasBasis.mem_of_mem, U_uni, antisymm, coverEntropyInf_eq_iSup_netEntropyInfEntourage, le_refl, mem_iff, mem_of_mem, netEntropyInfEntourage, netEntropyInfEntourage_antitone, si_U
-/
lemma coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage {ι : Sort*} {p : ι -> Prop}
    {s : ι -> SetRel X X} (h : (𝓤 X).HasBasis p s) (T : X -> X) (F : Set X) :
    coverEntropyInf T F = ⨆ (i : ι) (_ : p i), netEntropyInfEntourage T F (s i) := by
  rw [coverEntropyInf_eq_iSup_netEntropyInfEntourage T F]
  apply (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni => ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (netEntropyInfEntourage_antitone T F si_U).trans
  exact le_iSup₂ (f := fun (i : ι) (_ : p i) => netEntropyInfEntourage T F (s i)) i h_i

/--
lemma `coverEntropy_eq_iSup_basis_netEntropyEntourage` / 引理 `coverEntropy_eq_iSup_basis_netEntropyEntourage`

English:
lemma coverEntropy_eq_iSup_basis_netEntropyEntourage
  statement: {ι : Sort*} {p : ι -> Prop}
  proof: by
  rw [coverEntropy_eq_iSup_netEntropyEntourage T F]
  apply (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni => ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (netEntropyEntourage_antitone T F si_U).trans _
  exact 

中文:
引理 coverEntropy_eq_iSup_basis_netEntropyEntourage
  结论: {ι : Sort*} {p : ι -> 命题}
  证明: by
  rw [coverEntropy_eq_iSup_netEntropyEntourage T F]
  apply (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni => ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (netEntropyEntourage_antitone T F si_U).trans _
  exact 

Depends on / 依赖: HasBasis, HasBasis.mem_iff, HasBasis.mem_of_mem, U_uni, antisymm, coverEntropy_eq_iSup_netEntropyEntourage, le_refl, mem_iff, mem_of_mem, netEntropyEntourage, netEntropyEntourage_antitone, si_U
-/
lemma coverEntropy_eq_iSup_basis_netEntropyEntourage {ι : Sort*} {p : ι -> Prop}
    {s : ι -> SetRel X X} (h : (𝓤 X).HasBasis p s) (T : X -> X) (F : Set X) :
    coverEntropy T F = ⨆ (i : ι) (_ : p i), netEntropyEntourage T F (s i) := by
  rw [coverEntropy_eq_iSup_netEntropyEntourage T F]
  apply (iSup₂_mono' fun i h_i => ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni => ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (netEntropyEntourage_antitone T F si_U).trans _
  exact le_iSup₂ (f := fun (i : ι) (_ : p i) => netEntropyEntourage T F (s i)) i h_i

/--
lemma `netEntropyInfEntourage_le_coverEntropyInf` / 引理 `netEntropyInfEntourage_le_coverEntropyInf`

English:
lemma netEntropyInfEntourage_le_coverEntropyInf
  given: (h : U in 𝓤 X)
  proof: coverEntropyInf_eq_iSup_netEntropyInfEntourage T F ▸
    le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => netEntropyInfEntourage T F U) U h

中文:
引理 netEntropyInfEntourage_le_coverEntropyInf
  条件: (h : U in 𝓤 X)
  证明: coverEntropyInf_eq_iSup_netEntropyInfEntourage T F ▸
    le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => netEntropyInfEntourage T F U) U h

Depends on / 依赖: SetRel, coverEntropyInf_eq_iSup_netEntropyInfEntourage, netEntropyInfEntourage
-/
lemma netEntropyInfEntourage_le_coverEntropyInf (h : U in 𝓤 X) :
    netEntropyInfEntourage T F U <= coverEntropyInf T F :=
  coverEntropyInf_eq_iSup_netEntropyInfEntourage T F ▸
    le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => netEntropyInfEntourage T F U) U h

/--
lemma `netEntropyEntourage_le_coverEntropy` / 引理 `netEntropyEntourage_le_coverEntropy`

English:
lemma netEntropyEntourage_le_coverEntropy
  given: (h : U in 𝓤 X)
  proof: coverEntropy_eq_iSup_netEntropyEntourage T F ▸
    le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => netEntropyEntourage T F U) U h

中文:
引理 netEntropyEntourage_le_coverEntropy
  条件: (h : U in 𝓤 X)
  证明: coverEntropy_eq_iSup_netEntropyEntourage T F ▸
    le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => netEntropyEntourage T F U) U h

Depends on / 依赖: SetRel, coverEntropy_eq_iSup_netEntropyEntourage, netEntropyEntourage
-/
lemma netEntropyEntourage_le_coverEntropy (h : U in 𝓤 X) :
    netEntropyEntourage T F U <= coverEntropy T F :=
  coverEntropy_eq_iSup_netEntropyEntourage T F ▸
    le_iSup₂ (f := fun (U : SetRel X X) (_ : U in 𝓤 X) => netEntropyEntourage T F U) U h

end Dynamics
