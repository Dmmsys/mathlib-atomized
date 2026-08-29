/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Vlad Tsyrklevich
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card

/-!

# Maximal length of chains

This file contains lemmas to work with the maximal lengths of chains of arbitrary relations. See
`Order.height` for a definition specialized to finding the height of an element in a preorder.

## Main definition

- `Set.chainHeight`: The maximal length of a chain in a set `s` with relation `r`.

## Main results

- `Set.exists_isChain_of_le_chainHeight`: For each `n : ℕ` such that `n ≤ s.chainHeight`, there
  exists a subset `t` of length `n` such that `IsChain r t`.
- `Set.chainHeight_mono`: If `s ⊆ t` then `s.chainHeight ≤ t.chainHeight`.
- `Set.chainHeight_eq_of_relEmbedding`: If `f` is an relation embedding, then
  `(f '' s).chainHeight = s.chainHeight`.

-/

@[expose] public section

assert_not_exists Field

namespace Set

open ENat

variable {α β : Type*} (s : Set α) (r : α -> α -> Prop)

/--
Definition of `chainHeight` / `chainHeight` 的定义

English:
definition chainHeight
  signature: : Nat∞
  body: ⨆ t : {t : Set α // t subseteq s ∧ IsChain r t}, t.val.encard

中文:
定义 chainHeight
  签名: : 自然数∞
  定义体: ⨆ t : {t : Set α // t subseteq s ∧ IsChain r t}, t.val.encard

Depends on / 依赖: IsChain, encard, subseteq, t.val.encard
-/
noncomputable def chainHeight : Nat∞ := ⨆ t : {t : Set α // t subseteq s ∧ IsChain r t}, t.val.encard

/--
theorem `chainHeight_eq_iSup` / 定理 `chainHeight_eq_iSup`

English:
theorem chainHeight_eq_iSup
  proof: rfl

中文:
定理 chainHeight_eq_iSup
  证明: rfl
-/
theorem chainHeight_eq_iSup :
    s.chainHeight r = ⨆ t : {t : Set α // t subseteq s ∧ IsChain r t}, t.val.encard := rfl

/--
theorem `chainHeight_le_encard` / 定理 `chainHeight_le_encard`

English:
theorem chainHeight_le_encard
  statement: s.chainHeight r <= s.encard
  proof: by
  simp_all [chainHeight, encard_le_encard]

中文:
定理 chainHeight_le_encard
  结论: s.chainHeight r <= s.encard
  证明: by
  simp_all [chainHeight, encard_le_encard]

Depends on / 依赖: IsPrincipalIdealRing, IsPrincipalIdealRing.isDedekindDomain, chainHeight, encard_le_encard, isDedekindDomain
-/
theorem chainHeight_le_encard : s.chainHeight r <= s.encard := by
  simp_all [chainHeight, encard_le_encard]

/--
theorem `chainHeight_ne_top_of_finite` / 定理 `chainHeight_ne_top_of_finite`

English:
theorem chainHeight_ne_top_of_finite
  given: (h : s.Finite)
  statement: s.chainHeight r != ⊤
  proof: LT.lt.ne_top lt_of_le_of_lt (chainHeight_le_encard s r) lt_top_iff_ne_top.mpr
    encard_ne_top_iff.mpr h

中文:
定理 chainHeight_ne_top_of_finite
  条件: (h : s.Finite)
  结论: s.chainHeight r != ⊤
  证明: LT.lt.ne_top lt_of_le_of_lt (chainHeight_le_encard s r) lt_top_iff_ne_top.mpr
    encard_ne_top_iff.mpr h

Depends on / 依赖: LT.lt.ne_top, chainHeight_le_encard, encard_ne_top_iff, encard_ne_top_iff.mpr, lt_of_le_of_lt, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, ne_top
-/
theorem chainHeight_ne_top_of_finite (h : s.Finite) : s.chainHeight r != ⊤ :=
LT.lt.ne_top lt_of_le_of_lt (chainHeight_le_encard s r) lt_top_iff_ne_top.mpr
    encard_ne_top_iff.mpr h

/--
theorem `exists_isChain_of_le_chainHeight` / 定理 `exists_isChain_of_le_chainHeight`

English:
theorem exists_isChain_of_le_chainHeight
  given: {r} {s : Set α} (n : Nat) (h : n <= s.chainHeight r)
  proof: by
  by_cases h' : n = 0
  · exact ⟨∅, by simp [h']⟩
  · obtain ⟨t, ht₁, ht₂, ht₃⟩ : exists t subseteq s, IsChain r t ∧ n <= t.encard := by
      contrapose! h
refine iSup_lt_iff.mpr ⟨n - 1, ?_, fun m => ENat.le_sub_one_of_lt h m.1 m.2.1 m.2.2⟩
      exact_mod_cast Nat.sub_one_lt h'
    obtain ⟨u, h

中文:
定理 exists_isChain_of_le_chainHeight
  条件: {r} {s : Set α} (n : 自然数) (h : n <= s.chainHeight r)
  证明: by
  by_cases h' : n = 0
  · exact ⟨∅, by simp [h']⟩
  · obtain ⟨t, ht₁, ht₂, ht₃⟩ : exists t subseteq s, IsChain r t ∧ n <= t.encard := by
      contrapose! h
refine iSup_lt_iff.mpr ⟨n - 1, ?_, fun m => ENat.le_sub_one_of_lt h m.1 m.2.1 m.2.2⟩
      exact_mod_cast Nat.sub_one_lt h'
    obtain ⟨u, h

Depends on / 依赖: ENat.le_sub_one_of_lt, IsChain, Nat.sub_one_lt, contrapose, encard, exists_subset_encard_eq, iSup_lt_iff, iSup_lt_iff.mpr, le_sub_one_of_lt, sub_one_lt, subseteq, t.encard
-/
theorem exists_isChain_of_le_chainHeight {r} {s : Set α} (n : Nat) (h : n <= s.chainHeight r) :
    exists t subseteq s, t.encard = n ∧ IsChain r t := by
  by_cases h' : n = 0
  · exact ⟨∅, by simp [h']⟩
  · obtain ⟨t, ht₁, ht₂, ht₃⟩ : exists t subseteq s, IsChain r t ∧ n <= t.encard := by
      contrapose! h
refine iSup_lt_iff.mpr ⟨n - 1, ?_, fun m => ENat.le_sub_one_of_lt h m.1 m.2.1 m.2.2⟩
      exact_mod_cast Nat.sub_one_lt h'
    obtain ⟨u, hu₁, hu₂⟩ := exists_subset_encard_eq ht₃
    exact ⟨u, hu₁.trans ht₁, hu₂, ht₂.mono hu₁⟩

/--
theorem `exists_eq_chainHeight_of_chainHeight_ne_top` / 定理 `exists_eq_chainHeight_of_chainHeight_ne_top`

English:
theorem exists_eq_chainHeight_of_chainHeight_ne_top
  given: (h : s.chainHeight r != ⊤)
  proof: by
  have : Nonempty { t // t subseteq s ∧ IsChain r t } := ⟨∅, by simp⟩
  obtain ⟨t, ht⟩ := exists_eq_iSup_of_lt_top (by rwa [← chainHeight_eq_iSup, lt_top_iff_ne_top])
  exact ⟨t.1, t.2.1, ht, t.2.2⟩

中文:
定理 exists_eq_chainHeight_of_chainHeight_ne_top
  条件: (h : s.chainHeight r != ⊤)
  证明: by
  have : Nonempty { t // t subseteq s ∧ IsChain r t } := ⟨∅, by simp⟩
  obtain ⟨t, ht⟩ := exists_eq_iSup_of_lt_top (by rwa [← chainHeight_eq_iSup, lt_top_iff_ne_top])
  exact ⟨t.1, t.2.1, ht, t.2.2⟩

Depends on / 依赖: IsChain, Nonempty, chainHeight_eq_iSup, exists_eq_iSup_of_lt_top, lt_top_iff_ne_top, subseteq
-/
theorem exists_eq_chainHeight_of_chainHeight_ne_top (h : s.chainHeight r != ⊤) :
    exists t subseteq s, t.encard = s.chainHeight r ∧ IsChain r t := by
  have : Nonempty { t // t subseteq s ∧ IsChain r t } := ⟨∅, by simp⟩
  obtain ⟨t, ht⟩ := exists_eq_iSup_of_lt_top (by rwa [← chainHeight_eq_iSup, lt_top_iff_ne_top])
  exact ⟨t.1, t.2.1, ht, t.2.2⟩

/--
theorem `exists_eq_chainHeight_of_finite` / 定理 `exists_eq_chainHeight_of_finite`

English:
theorem exists_eq_chainHeight_of_finite
  given: (h : s.Finite)
  proof: exists_eq_chainHeight_of_chainHeight_ne_top s r (chainHeight_ne_top_of_finite s r h)

中文:
定理 exists_eq_chainHeight_of_finite
  条件: (h : s.Finite)
  证明: exists_eq_chainHeight_of_chainHeight_ne_top s r (chainHeight_ne_top_of_finite s r h)

Depends on / 依赖: chainHeight_ne_top_of_finite, exists_eq_chainHeight_of_chainHeight_ne_top
-/
theorem exists_eq_chainHeight_of_finite (h : s.Finite) :
     exists t subseteq s, t.encard = s.chainHeight r ∧ IsChain r t :=
  exists_eq_chainHeight_of_chainHeight_ne_top s r (chainHeight_ne_top_of_finite s r h)

/--
theorem `encard_le_chainHeight_of_isChain` / 定理 `encard_le_chainHeight_of_isChain`

English:
theorem encard_le_chainHeight_of_isChain
  given: {r} (s t : Set α) (hs : t subseteq s) (hc : IsChain r t)
  proof: le_iSup_iff.mpr fun _ hb => hb ⟨t, hs, hc⟩

中文:
定理 encard_le_chainHeight_of_isChain
  条件: {r} (s t : Set α) (hs : t subseteq s) (hc : IsChain r t)
  证明: le_iSup_iff.mpr fun _ hb => hb ⟨t, hs, hc⟩

Depends on / 依赖: le_iSup_iff, le_iSup_iff.mpr
-/
theorem encard_le_chainHeight_of_isChain {r} (s t : Set α) (hs : t subseteq s) (hc : IsChain r t) :
    t.encard <= s.chainHeight r :=
  le_iSup_iff.mpr fun _ hb => hb ⟨t, hs, hc⟩

/--
theorem `encard_eq_chainHeight_of_isChain` / 定理 `encard_eq_chainHeight_of_isChain`

English:
theorem encard_eq_chainHeight_of_isChain
  given: {r} (s : Set α) (hc : IsChain r s)
  proof: le_antisymm (encard_le_chainHeight_of_isChain _ _ Set.Subset.rfl hc) (chainHeight_le_encard _ _)

中文:
定理 encard_eq_chainHeight_of_isChain
  条件: {r} (s : Set α) (hc : IsChain r s)
  证明: le_antisymm (encard_le_chainHeight_of_isChain _ _ Set.Subset.rfl hc) (chainHeight_le_encard _ _)

Depends on / 依赖: Set.Subset.rfl, Subset, chainHeight_le_encard, encard_le_chainHeight_of_isChain, le_antisymm
-/
theorem encard_eq_chainHeight_of_isChain {r} (s : Set α) (hc : IsChain r s) :
    s.encard = s.chainHeight r :=
  le_antisymm (encard_le_chainHeight_of_isChain _ _ Set.Subset.rfl hc) (chainHeight_le_encard _ _)

/--
theorem `finite_of_chainHeight_ne_top` / 定理 `finite_of_chainHeight_ne_top`

English:
theorem finite_of_chainHeight_ne_top
  given: {r} {s : Set α} (hc : IsChain r s) (h : s.chainHeight r != ⊤)
  proof: Set.encard_ne_top_iff.mp ne_top_of_le_ne_top h
    encard_le_chainHeight_of_isChain _ _ (subset_refl _) hc

中文:
定理 finite_of_chainHeight_ne_top
  条件: {r} {s : Set α} (hc : IsChain r s) (h : s.chainHeight r != ⊤)
  证明: Set.encard_ne_top_iff.mp ne_top_of_le_ne_top h
    encard_le_chainHeight_of_isChain _ _ (subset_refl _) hc

Depends on / 依赖: Set.encard_ne_top_iff.mp, encard_le_chainHeight_of_isChain, encard_ne_top_iff, ne_top_of_le_ne_top, subset_refl
-/
theorem finite_of_chainHeight_ne_top {r} {s : Set α} (hc : IsChain r s) (h : s.chainHeight r != ⊤) :
    s.Finite :=
Set.encard_ne_top_iff.mp ne_top_of_le_ne_top h
    encard_le_chainHeight_of_isChain _ _ (subset_refl _) hc

/--
theorem `not_isChain_of_chainHeight_lt_encard` / 定理 `not_isChain_of_chainHeight_lt_encard`

English:
theorem not_isChain_of_chainHeight_lt_encard
  statement: (s t : Set α) (ht : t subseteq s)
  proof: by
  by_contra! hh
  grw [encard_le_chainHeight_of_isChain _ _ ht hh] at he
  exact (lt_self_iff_false _).mp he

中文:
定理 not_isChain_of_chainHeight_lt_encard
  结论: (s t : Set α) (ht : t subseteq s)
  证明: by
  by_contra! hh
  grw [encard_le_chainHeight_of_isChain _ _ ht hh] at he
  exact (lt_self_iff_false _).mp he

Depends on / 依赖: encard_le_chainHeight_of_isChain, lt_self_iff_false
-/
theorem not_isChain_of_chainHeight_lt_encard (s t : Set α) (ht : t subseteq s)
    (he : s.chainHeight r < t.encard) : ¬ IsChain r t := by
  by_contra! hh
  grw [encard_le_chainHeight_of_isChain _ _ ht hh] at he
  exact (lt_self_iff_false _).mp he

/--
theorem `chainHeight_eq_top_iff` / 定理 `chainHeight_eq_top_iff`

English:
theorem chainHeight_eq_top_iff
  proof: by
  refine ⟨fun h _ => exists_isChain_of_le_chainHeight _ (le_top.trans_eq h.symm), fun h => ?_⟩
  contrapose! h
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  refine ⟨n + 1, fun l hl he => not_isChain_of_chainHeight_lt_encard r s l hl ?_⟩
  rw [← hn]; rw [he]
  exact_mod_cast lt_add_one _

@[si

中文:
定理 chainHeight_eq_top_iff
  证明: by
  refine ⟨fun h _ => exists_isChain_of_le_chainHeight _ (le_top.trans_eq h.symm), fun h => ?_⟩
  contrapose! h
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  refine ⟨n + 1, fun l hl he => not_isChain_of_chainHeight_lt_encard r s l hl ?_⟩
  rw [← hn]; rw [he]
  exact_mod_cast lt_add_one _

@[si

Depends on / 依赖: ENat.ne_top_iff_exists.mp, contrapose, exists_isChain_of_le_chainHeight, h.symm, le_top, le_top.trans_eq, lt_add_one, ne_top_iff_exists, not_isChain_of_chainHeight_lt_encard, trans_eq
-/
theorem chainHeight_eq_top_iff :
    s.chainHeight r = ⊤ ↔ forall n : Nat, exists t subseteq s, t.encard = n ∧ IsChain r t := by
  refine ⟨fun h _ => exists_isChain_of_le_chainHeight _ (le_top.trans_eq h.symm), fun h => ?_⟩
  contrapose! h
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  refine ⟨n + 1, fun l hl he => not_isChain_of_chainHeight_lt_encard r s l hl ?_⟩
  rw [← hn]; rw [he]
  exact_mod_cast lt_add_one _

@[simp]
/--
theorem `chainHeight_eq_zero_iff` / 定理 `chainHeight_eq_zero_iff`

English:
theorem chainHeight_eq_zero_iff
  statement: s.chainHeight r = 0 ↔ s = ∅
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [chainHeight, iSup_eq_zero, encard_eq_zero, Subtype.forall, and_imp] at h
    ext x
    simpa using h {x}
  · simp_all [chainHeight]

@[simp]

中文:
定理 chainHeight_eq_zero_iff
  结论: s.chainHeight r = 0 ↔ s = ∅
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [chainHeight, iSup_eq_zero, encard_eq_zero, Subtype.forall, and_imp] at h
    ext x
    simpa using h {x}
  · simp_all [chainHeight]

@[simp]

Depends on / 依赖: Subtype, Subtype.forall, and_imp, chainHeight, encard_eq_zero, iSup_eq_zero
-/
theorem chainHeight_eq_zero_iff : s.chainHeight r = 0 ↔ s = ∅ := by
  refine ⟨fun h => ?_, ?_⟩
  · simp only [chainHeight, iSup_eq_zero, encard_eq_zero, Subtype.forall, and_imp] at h
    ext x
    simpa using h {x}
  · simp_all [chainHeight]

@[simp]
/--
theorem `chainHeight_empty` / 定理 `chainHeight_empty`

English:
theorem chainHeight_empty
  statement: (∅ : Set α).chainHeight r = 0
  proof: .mpr rfl chainHeight_eq_zero_iff _ _

@[simp]

中文:
定理 chainHeight_empty
  结论: (∅ : Set α).chainHeight r = 0
  证明: .mpr rfl chainHeight_eq_zero_iff _ _

@[simp]

Depends on / 依赖: chainHeight_eq_zero_iff
-/
theorem chainHeight_empty : (∅ : Set α).chainHeight r = 0 :=
.mpr rfl chainHeight_eq_zero_iff _ _

@[simp]
/--
theorem `one_le_chainHeight_iff` / 定理 `one_le_chainHeight_iff`

English:
theorem one_le_chainHeight_iff
  statement: 1 <= s.chainHeight r ↔ s.Nonempty
  proof: by
  constructor
  all_goals
  · intros
    by_contra! hh
    simp_all

@[simp]

中文:
定理 one_le_chainHeight_iff
  结论: 1 <= s.chainHeight r ↔ s.Nonempty
  证明: by
  constructor
  all_goals
  · intros
    by_contra! hh
    simp_all

@[simp]

Depends on / 依赖: all_goals, intros
-/
theorem one_le_chainHeight_iff : 1 <= s.chainHeight r ↔ s.Nonempty := by
  constructor
  all_goals
  · intros
    by_contra! hh
    simp_all

@[simp]
/--
theorem `chainHeight_of_isEmpty` / 定理 `chainHeight_of_isEmpty`

English:
theorem chainHeight_of_isEmpty
  given: [IsEmpty α]
  statement: s.chainHeight r = 0
  proof: .mpr (Subsingleton.elim _ _) chainHeight_eq_zero_iff s r

@[gcongr, mono]

中文:
定理 chainHeight_of_isEmpty
  条件: [IsEmpty α]
  结论: s.chainHeight r = 0
  证明: .mpr (Subsingleton.elim _ _) chainHeight_eq_zero_iff s r

@[gcongr, mono]

Depends on / 依赖: Subsingleton, Subsingleton.elim, chainHeight_eq_zero_iff
-/
theorem chainHeight_of_isEmpty [IsEmpty α] : s.chainHeight r = 0 :=
.mpr (Subsingleton.elim _ _) chainHeight_eq_zero_iff s r

@[gcongr, mono]
/--
theorem `chainHeight_mono` / 定理 `chainHeight_mono`

English:
theorem chainHeight_mono
  given: (s t : Set α) (h : s subseteq t)
  statement: s.chainHeight r <= t.chainHeight r
  proof: by
  refine forall_natCast_le_iff_le.mp fun n hn => ?_
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
  exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ (ha₁.trans h) ha₃

@[simp]

中文:
定理 chainHeight_mono
  条件: (s t : Set α) (h : s subseteq t)
  结论: s.chainHeight r <= t.chainHeight r
  证明: by
  refine forall_natCast_le_iff_le.mp fun n hn => ?_
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
  exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ (ha₁.trans h) ha₃

@[simp]

Depends on / 依赖: encard_le_chainHeight_of_isChain, exists_isChain_of_le_chainHeight, forall_natCast_le_iff_le, forall_natCast_le_iff_le.mp
-/
theorem chainHeight_mono (s t : Set α) (h : s subseteq t) : s.chainHeight r <= t.chainHeight r := by
  refine forall_natCast_le_iff_le.mp fun n hn => ?_
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
  exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ (ha₁.trans h) ha₃

@[simp]
/--
theorem `chainHeight_flip` / 定理 `chainHeight_flip`

English:
theorem chainHeight_flip
  statement: s.chainHeight (flip r) = s.chainHeight r
  proof: by
  refine eq_of_forall_natCast_le_iff fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  all_goals
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ ha₁
      fun _ hx _ hy hne => by simpa [flip, Or.comm] using ha₃ hx hy hne

中文:
定理 chainHeight_flip
  结论: s.chainHeight (flip r) = s.chainHeight r
  证明: by
  refine eq_of_forall_natCast_le_iff fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  all_goals
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ ha₁
      fun _ hx _ hy hne => by simpa [flip, Or.comm] using ha₃ hx hy hne

Depends on / 依赖: Or.comm, all_goals, encard_le_chainHeight_of_isChain, eq_of_forall_natCast_le_iff, exists_isChain_of_le_chainHeight
-/
theorem chainHeight_flip : s.chainHeight (flip r) = s.chainHeight r := by
  refine eq_of_forall_natCast_le_iff fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  all_goals
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
exact ha₂ ▸ encard_le_chainHeight_of_isChain _ _ ha₁
      fun _ hx _ hy hne => by simpa [flip, Or.comm] using ha₃ hx hy hne

section Rel

variable {r : α -> α -> Prop} {r' : β -> β -> Prop} (s : Set α)

/--
theorem `chainHeight_eq_of_relEmbedding` / 定理 `chainHeight_eq_of_relEmbedding`

English:
theorem chainHeight_eq_of_relEmbedding
  given: (e : r ↪r r')
  proof: by
  refine eq_of_forall_natCast_le_iff fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    rw [← ha₂]; rw [← Set.encard_preimage_of_injective_subset_range e.injective (by grind)]
exact encard_le_chainHeight_of_isChain _ _ (preimage_subset

中文:
定理 chainHeight_eq_of_relEmbedding
  条件: (e : r ↪r r')
  证明: by
  refine eq_of_forall_natCast_le_iff fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    rw [← ha₂]; rw [← Set.encard_preimage_of_injective_subset_range e.injective (by grind)]
exact encard_le_chainHeight_of_isChain _ _ (preimage_subset

Depends on / 依赖: Set.encard_preimage_of_injective_subset_range, e.injective, e.injective.encard_image, e.injective.injOn, encard_image, encard_le_chainHeight_of_isChain, encard_preimage_of_injective_subset_range, eq_of_forall_natCast_le_iff, exists_isChain_of_le_chainHeight, injective, preimage_relEmbedding, preimage_subset
-/
theorem chainHeight_eq_of_relEmbedding (e : r ↪r r') :
    (e '' s).chainHeight r' = s.chainHeight r := by
  refine eq_of_forall_natCast_le_iff fun n => ⟨fun hn => ?_, fun hn => ?_⟩
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    rw [← ha₂]; rw [← Set.encard_preimage_of_injective_subset_range e.injective (by grind)]
exact encard_le_chainHeight_of_isChain _ _ (preimage_subset ha₁ e.injective.injOn)
      ha₃.preimage_relEmbedding e
  · obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_isChain_of_le_chainHeight n hn
    rw [← ha₂]; rw [← e.injective.encard_image]
exact encard_le_chainHeight_of_isChain _ _ (by grind) ha₃.image e

/--
theorem `chainHeight_eq_of_relIso` / 定理 `chainHeight_eq_of_relIso`

English:
theorem chainHeight_eq_of_relIso
  given: (e : r ≃r r')
  statement: (e '' s).chainHeight r' = s.chainHeight r
  proof: chainHeight_eq_of_relEmbedding s e.toRelEmbedding

中文:
定理 chainHeight_eq_of_relIso
  条件: (e : r ≃r r')
  结论: (e '' s).chainHeight r' = s.chainHeight r
  证明: chainHeight_eq_of_relEmbedding s e.toRelEmbedding

Depends on / 依赖: chainHeight_eq_of_relEmbedding, e.toRelEmbedding, toRelEmbedding
-/
theorem chainHeight_eq_of_relIso (e : r ≃r r') : (e '' s).chainHeight r' = s.chainHeight r :=
  chainHeight_eq_of_relEmbedding s e.toRelEmbedding

end Rel

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `chainHeight_coe_univ` / 定理 `chainHeight_coe_univ`

English:
theorem chainHeight_coe_univ
  statement: (@Set.univ ↑s).chainHeight (r ↑· ↑·) = s.chainHeight r
  proof: by
have hc := Set.chainHeight_eq_of_relEmbedding univ Subtype.relEmbedding (r · ·) (· in s)
  have hs : Subtype.val ⁻¹'o (r · ·) = (fun x y : s => r x y) := by funext; simp
  simpa [hs] using hc.symm

@[simp]

中文:
定理 chainHeight_coe_univ
  结论: (@Set.univ ↑s).chainHeight (r ↑· ↑·) = s.chainHeight r
  证明: by
have hc := Set.chainHeight_eq_of_relEmbedding univ Subtype.relEmbedding (r · ·) (· in s)
  have hs : Subtype.val ⁻¹'o (r · ·) = (fun x y : s => r x y) := by funext; simp
  simpa [hs] using hc.symm

@[simp]

Depends on / 依赖: Set.chainHeight_eq_of_relEmbedding, Subtype, Subtype.relEmbedding, Subtype.val, chainHeight_eq_of_relEmbedding, hc.symm, relEmbedding
-/
theorem chainHeight_coe_univ : (@Set.univ ↑s).chainHeight (r ↑· ↑·) = s.chainHeight r := by
have hc := Set.chainHeight_eq_of_relEmbedding univ Subtype.relEmbedding (r · ·) (· in s)
  have hs : Subtype.val ⁻¹'o (r · ·) = (fun x y : s => r x y) := by funext; simp
  simpa [hs] using hc.symm

@[simp]
/--
theorem `chainHeight_coe_univ_le` / 定理 `chainHeight_coe_univ_le`

English:
theorem chainHeight_coe_univ_le
  given: [LE α]
  proof: by
  simpa using chainHeight_coe_univ s (· <= ·)

@[simp]

中文:
定理 chainHeight_coe_univ_le
  条件: [LE α]
  证明: by
  simpa using chainHeight_coe_univ s (· <= ·)

@[simp]

Depends on / 依赖: chainHeight_coe_univ
-/
theorem chainHeight_coe_univ_le [LE α] :
    (@Set.univ ↑s).chainHeight (· <= ·) = s.chainHeight (· <= ·) := by
  simpa using chainHeight_coe_univ s (· <= ·)

@[simp]
/--
theorem `chainHeight_coe_univ_lt` / 定理 `chainHeight_coe_univ_lt`

English:
theorem chainHeight_coe_univ_lt
  given: [LT α]
  proof: by
  simpa using chainHeight_coe_univ s (· < ·)

中文:
定理 chainHeight_coe_univ_lt
  条件: [LT α]
  证明: by
  simpa using chainHeight_coe_univ s (· < ·)

Depends on / 依赖: chainHeight_coe_univ
-/
theorem chainHeight_coe_univ_lt [LT α] :
    (@Set.univ ↑s).chainHeight (· < ·) = s.chainHeight (· < ·) := by
  simpa using chainHeight_coe_univ s (· < ·)

end Set
