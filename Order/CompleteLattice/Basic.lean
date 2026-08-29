/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.NAry
public import Mathlib.Data.ULift
public import Mathlib.Order.Bounds.Image
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Hom.Set

/-!
# Theory of complete lattices

This file contains basic results on complete lattices.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`.
-/

public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι -> Sort*} {κ' : ι' -> Sort*}

/--
lemma `iSup_ulift` / 引理 `iSup_ulift`

English:
lemma iSup_ulift
  given: {ι : Type*} [SupSet α] (f : ULift ι -> α)
  proof: by simp only [iSup]; congr with x; simp

中文:
引理 iSup_ulift
  条件: {ι : 类型} [SupSet α] (f : ULift ι -> α)
  证明: by simp only [iSup]; congr with x; simp
-/
@[to_dual (attr := simp)] lemma iSup_ulift {ι : Type*} [SupSet α] (f : ULift ι -> α) :
    ⨆ i : ULift ι, f i = ⨆ i, f (.up i) := by simp only [iSup]; congr with x; simp

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

@[to_dual]
/--
theorem `sSup_le_sSup_of_isCofinalFor` / 定理 `sSup_le_sSup_of_isCofinalFor`

English:
theorem sSup_le_sSup_of_isCofinalFor
  given: (h : IsCofinalFor s t)
  statement: sSup s <= sSup t
  proof: IsLeast.mono (isLUB_sSup t) (isLUB_sSup s) upperBounds_mono_of_isCofinalFor h

中文:
定理 sSup_le_sSup_of_isCofinalFor
  条件: (h : IsCofinalFor s t)
  结论: sSup s <= sSup t
  证明: IsLeast.mono (isLUB_sSup t) (isLUB_sSup s) upperBounds_mono_of_isCofinalFor h

Depends on / 依赖: IsLeast, IsLeast.mono, isLUB_sSup, upperBounds_mono_of_isCofinalFor
-/
theorem sSup_le_sSup_of_isCofinalFor (h : IsCofinalFor s t) : sSup s <= sSup t :=
IsLeast.mono (isLUB_sSup t) (isLUB_sSup s) upperBounds_mono_of_isCofinalFor h

-- We will generalize this to conditionally complete lattices in `csSup_singleton`.
@[to_dual (attr := simp)]
/--
theorem `sSup_singleton` / 定理 `sSup_singleton`

English:
theorem sSup_singleton
  given: {a : α}
  statement: sSup {a} = a
  proof: isLUB_singleton.sSup_eq

中文:
定理 sSup_singleton
  条件: {a : α}
  结论: sSup {a} = a
  证明: isLUB_singleton.sSup_eq

Depends on / 依赖: isLUB_singleton, isLUB_singleton.sSup_eq, sSup_eq
-/
theorem sSup_singleton {a : α} : sSup {a} = a :=
  isLUB_singleton.sSup_eq

end

open OrderDual

section

variable [CompleteLattice α] {s t : Set α} {b : α}

/--
theorem `sInf_le_sSup` / 定理 `sInf_le_sSup`

English:
theorem sInf_le_sSup
  given: (hs : s.Nonempty)
  statement: sInf s <= sSup s
  proof: isGLB_le_isLUB (isGLB_sInf s) (isLUB_sSup s) hs

中文:
定理 sInf_le_sSup
  条件: (hs : s.Nonempty)
  结论: sInf s <= sSup s
  证明: isGLB_le_isLUB (isGLB_sInf s) (isLUB_sSup s) hs

Depends on / 依赖: isGLB_le_isLUB, isGLB_sInf, isLUB_sSup
-/
theorem sInf_le_sSup (hs : s.Nonempty) : sInf s <= sSup s :=
  isGLB_le_isLUB (isGLB_sInf s) (isLUB_sSup s) hs

/--
theorem `sInf_le_sSup_of_nonempty_inter` / 定理 `sInf_le_sSup_of_nonempty_inter`

English:
theorem sInf_le_sSup_of_nonempty_inter
  given: (h : (s inter t).Nonempty)
  statement: sInf s <= sSup t
  proof: isGLB_le_isLUB_of_nonempty_inter h (isGLB_sInf s) (isLUB_sSup t)

@[to_dual]

中文:
定理 sInf_le_sSup_of_nonempty_inter
  条件: (h : (s inter t).Nonempty)
  结论: sInf s <= sSup t
  证明: isGLB_le_isLUB_of_nonempty_inter h (isGLB_sInf s) (isLUB_sSup t)

@[to_dual]

Depends on / 依赖: isGLB_le_isLUB_of_nonempty_inter, isGLB_sInf, isLUB_sSup
-/
theorem sInf_le_sSup_of_nonempty_inter (h : (s inter t).Nonempty) : sInf s <= sSup t :=
  isGLB_le_isLUB_of_nonempty_inter h (isGLB_sInf s) (isLUB_sSup t)

@[to_dual]
/--
theorem `sSup_union` / 定理 `sSup_union`

English:
theorem sSup_union
  given: {s t : Set α}
  statement: sSup (s union t) = sSup s ⊔ sSup t
  proof: ((isLUB_sSup s).union (isLUB_sSup t)).sSup_eq

@[to_dual le_sInf_inter]

中文:
定理 sSup_union
  条件: {s t : Set α}
  结论: sSup (s union t) = sSup s ⊔ sSup t
  证明: ((isLUB_sSup s).union (isLUB_sSup t)).sSup_eq

@[to_dual le_sInf_inter]

Depends on / 依赖: isLUB_sSup, sSup_eq
-/
theorem sSup_union {s t : Set α} : sSup (s union t) = sSup s ⊔ sSup t :=
  ((isLUB_sSup s).union (isLUB_sSup t)).sSup_eq

@[to_dual le_sInf_inter]
/--
theorem `sSup_inter_le` / 定理 `sSup_inter_le`

English:
theorem sSup_inter_le
  given: {s t : Set α}
  statement: sSup (s inter t) <= sSup s ⊓ sSup t
  proof: sSup_le fun _ hb => le_inf (le_sSup hb.1) (le_sSup hb.2)

@[to_dual (attr := simp)]

中文:
定理 sSup_inter_le
  条件: {s t : Set α}
  结论: sSup (s inter t) <= sSup s ⊓ sSup t
  证明: sSup_le fun _ hb => le_inf (le_sSup hb.1) (le_sSup hb.2)

@[to_dual (attr := simp)]

Depends on / 依赖: le_inf, le_sSup, sSup_le
-/
theorem sSup_inter_le {s t : Set α} : sSup (s inter t) <= sSup s ⊓ sSup t :=
  sSup_le fun _ hb => le_inf (le_sSup hb.1) (le_sSup hb.2)

@[to_dual (attr := simp)]
/--
theorem `sSup_empty` / 定理 `sSup_empty`

English:
theorem sSup_empty
  statement: sSup ∅ = (⊥ : α)
  proof: (@isLUB_empty α _ _).sSup_eq

@[to_dual (attr := simp)]

中文:
定理 sSup_empty
  结论: sSup ∅ = (⊥ : α)
  证明: (@isLUB_empty α _ _).sSup_eq

@[to_dual (attr := simp)]

Depends on / 依赖: isLUB_empty, sSup_eq
-/
theorem sSup_empty : sSup ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).sSup_eq

@[to_dual (attr := simp)]
/--
theorem `sSup_univ` / 定理 `sSup_univ`

English:
theorem sSup_univ
  statement: sSup univ = (⊤ : α)
  proof: (@isLUB_univ α _ _).sSup_eq

中文:
定理 sSup_univ
  结论: sSup univ = (⊤ : α)
  证明: (@isLUB_univ α _ _).sSup_eq

Depends on / 依赖: isLUB_univ, sSup_eq
-/
theorem sSup_univ : sSup univ = (⊤ : α) :=
  (@isLUB_univ α _ _).sSup_eq

-- TODO(Jeremy): get this automatically
@[to_dual (attr := simp)]
/--
theorem `sSup_insert` / 定理 `sSup_insert`

English:
theorem sSup_insert
  given: {a : α} {s : Set α}
  statement: sSup (insert a s) = a ⊔ sSup s
  proof: ((isLUB_sSup s).insert a).sSup_eq

@[to_dual]

中文:
定理 sSup_insert
  条件: {a : α} {s : Set α}
  结论: sSup (insert a s) = a ⊔ sSup s
  证明: ((isLUB_sSup s).insert a).sSup_eq

@[to_dual]

Depends on / 依赖: insert, isLUB_sSup, sSup_eq
-/
theorem sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_sSup s).insert a).sSup_eq

@[to_dual]
/--
theorem `sSup_le_sSup_of_subset_insert_bot` / 定理 `sSup_le_sSup_of_subset_insert_bot`

English:
theorem sSup_le_sSup_of_subset_insert_bot
  given: (h : s subseteq insert ⊥ t)
  statement: sSup s <= sSup t
  proof: (sSup_le_sSup h).trans_eq (sSup_insert.trans (bot_sup_eq _))

@[to_dual (attr := simp)]

中文:
定理 sSup_le_sSup_of_subset_insert_bot
  条件: (h : s subseteq insert ⊥ t)
  结论: sSup s <= sSup t
  证明: (sSup_le_sSup h).trans_eq (sSup_insert.trans (bot_sup_eq _))

@[to_dual (attr := simp)]

Depends on / 依赖: bot_sup_eq, sSup_insert, sSup_insert.trans, sSup_le_sSup, trans_eq
-/
theorem sSup_le_sSup_of_subset_insert_bot (h : s subseteq insert ⊥ t) : sSup s <= sSup t :=
  (sSup_le_sSup h).trans_eq (sSup_insert.trans (bot_sup_eq _))

@[to_dual (attr := simp)]
/--
theorem `sSup_sdiff_singleton_bot` / 定理 `sSup_sdiff_singleton_bot`

English:
theorem sSup_sdiff_singleton_bot
  given: (s : Set α)
  statement: sSup (s \ {⊥}) = sSup s
  proof: (sSup_le_sSup sdiff_subset).antisymm
sSup_le_sSup_of_subset_insert_bot subset_insert_sdiff_singleton _ _

@[deprecated (since := "2026-06-03")] alias sSup_diff_singleton_bot := sSup_sdiff_singleton_bot

@[to_dual]

中文:
定理 sSup_sdiff_singleton_bot
  条件: (s : Set α)
  结论: sSup (s \ {⊥}) = sSup s
  证明: (sSup_le_sSup sdiff_subset).antisymm
sSup_le_sSup_of_subset_insert_bot subset_insert_sdiff_singleton _ _

@[deprecated (since := "2026-06-03")] alias sSup_diff_singleton_bot := sSup_sdiff_singleton_bot

@[to_dual]

Depends on / 依赖: antisymm, sSup_le_sSup, sSup_le_sSup_of_subset_insert_bot, sdiff_subset, subset_insert_sdiff_singleton
-/
theorem sSup_sdiff_singleton_bot (s : Set α) : sSup (s \ {⊥}) = sSup s :=
(sSup_le_sSup sdiff_subset).antisymm
sSup_le_sSup_of_subset_insert_bot subset_insert_sdiff_singleton _ _

@[deprecated (since := "2026-06-03")] alias sSup_diff_singleton_bot := sSup_sdiff_singleton_bot

@[to_dual]
/--
theorem `sSup_pair` / 定理 `sSup_pair`

English:
theorem sSup_pair
  given: {a b : α}
  statement: sSup {a, b} = a ⊔ b
  proof: (@isLUB_pair α _ a b).sSup_eq

@[to_dual (attr := simp)]

中文:
定理 sSup_pair
  条件: {a b : α}
  结论: sSup {a, b} = a ⊔ b
  证明: (@isLUB_pair α _ a b).sSup_eq

@[to_dual (attr := simp)]

Depends on / 依赖: isLUB_pair, sSup_eq
-/
theorem sSup_pair {a b : α} : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair α _ a b).sSup_eq

@[to_dual (attr := simp)]
/--
theorem `sSup_eq_bot` / 定理 `sSup_eq_bot`

English:
theorem sSup_eq_bot
  statement: sSup s = ⊥ ↔ forall a in s, a = ⊥
  proof: ⟨fun h _ ha => bot_unique h ▸ le_sSup ha, fun h =>
bot_unique sSup_le fun a ha => le_bot_iff.2 h a ha⟩

@[to_dual]

中文:
定理 sSup_eq_bot
  结论: sSup s = ⊥ ↔ 对任意 a in s, a = ⊥
  证明: ⟨fun h _ ha => bot_unique h ▸ le_sSup ha, fun h =>
bot_unique sSup_le fun a ha => le_bot_iff.2 h a ha⟩

@[to_dual]

Depends on / 依赖: bot_unique, le_bot_iff, le_sSup, sSup_le
-/
theorem sSup_eq_bot : sSup s = ⊥ ↔ forall a in s, a = ⊥ :=
⟨fun h _ ha => bot_unique h ▸ le_sSup ha, fun h =>
bot_unique sSup_le fun a ha => le_bot_iff.2 h a ha⟩

@[to_dual]
/--
lemma `sSup_eq_bot'` / 引理 `sSup_eq_bot'`

English:
lemma sSup_eq_bot'
  given: {s : Set α}
  statement: sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥}
  proof: by
  rw [sSup_eq_bot]; rw [← subset_singleton_iff_eq]; rw [subset_singleton_iff]

@[to_dual]

中文:
引理 sSup_eq_bot'
  条件: {s : Set α}
  结论: sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥}
  证明: by
  rw [sSup_eq_bot]; rw [← subset_singleton_iff_eq]; rw [subset_singleton_iff]

@[to_dual]

Depends on / 依赖: sSup_eq_bot, subset_singleton_iff, subset_singleton_iff_eq
-/
lemma sSup_eq_bot' {s : Set α} : sSup s = ⊥ ↔ s = ∅ ∨ s = {⊥} := by
  rw [sSup_eq_bot]; rw [← subset_singleton_iff_eq]; rw [subset_singleton_iff]

@[to_dual]
/--
theorem `eq_singleton_bot_of_sSup_eq_bot_of_nonempty` / 定理 `eq_singleton_bot_of_sSup_eq_bot_of_nonempty`

English:
theorem eq_singleton_bot_of_sSup_eq_bot_of_nonempty
  statement: {s : Set α} (h_sup : sSup s = ⊥)
  proof: by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [sSup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩

中文:
定理 eq_singleton_bot_of_sSup_eq_bot_of_nonempty
  结论: {s : Set α} (h_sup : sSup s = ⊥)
  证明: by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [sSup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩

Depends on / 依赖: Set.eq_singleton_iff_nonempty_unique_mem, eq_singleton_iff_nonempty_unique_mem, h_sup, sSup_eq_bot
-/
theorem eq_singleton_bot_of_sSup_eq_bot_of_nonempty {s : Set α} (h_sup : sSup s = ⊥)
    (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [sSup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `csSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
@[to_dual sInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `csInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/]
/--
theorem `sSup_eq_of_forall_le_of_forall_lt_exists_gt` / 定理 `sSup_eq_of_forall_le_of_forall_lt_exists_gt`

English:
theorem sSup_eq_of_forall_le_of_forall_lt_exists_gt
  statement: (h₁ : forall a in s, a <= b)
  proof: (sSup_le h₁).eq_of_not_lt fun h =>
    let ⟨_, ha, ha'⟩ := h₂ _ h
    ((le_sSup ha).trans_lt ha').false

中文:
定理 sSup_eq_of_forall_le_of_forall_lt_exists_gt
  结论: (h₁ : 对任意 a in s, a <= b)
  证明: (sSup_le h₁).eq_of_not_lt fun h =>
    let ⟨_, ha, ha'⟩ := h₂ _ h
    ((le_sSup ha).trans_lt ha').false

Depends on / 依赖: eq_of_not_lt, le_sSup, sSup_le, trans_lt
-/
theorem sSup_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : forall a in s, a <= b)
    (h₂ : forall w, w < b -> exists a in s, w < a) : sSup s = b :=
  (sSup_le h₁).eq_of_not_lt fun h =>
    let ⟨_, ha, ha'⟩ := h₂ _ h
    ((le_sSup ha).trans_lt ha').false

end

/-
### iSup & iInf
-/
section SupSet

variable [SupSet α] {f g : ι -> α}

@[to_dual]
/--
theorem `sSup_range` / 定理 `sSup_range`

English:
theorem sSup_range
  statement: sSup (range f) = iSup f
  proof: rfl

@[to_dual]

中文:
定理 sSup_range
  结论: sSup (range f) = iSup f
  证明: rfl

@[to_dual]
-/
theorem sSup_range : sSup (range f) = iSup f :=
  rfl

@[to_dual]
/--
theorem `sSup_eq_iSup'` / 定理 `sSup_eq_iSup'`

English:
theorem sSup_eq_iSup'
  given: (s : Set α)
  statement: sSup s = ⨆ a : s, (a : α)
  proof: by rw [iSup, Subtype.range_coe]

@[to_dual]

中文:
定理 sSup_eq_iSup'
  条件: (s : Set α)
  结论: sSup s = ⨆ a : s, (a : α)
  证明: by rw [iSup, Subtype.range_coe]

@[to_dual]

Depends on / 依赖: Subtype, Subtype.range_coe, range_coe
-/
theorem sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α) := by rw [iSup, Subtype.range_coe]

@[to_dual]
/--
theorem `iSup_congr` / 定理 `iSup_congr`

English:
theorem iSup_congr
  given: (h : forall i, f i = g i)
  statement: ⨆ i, f i = ⨆ i, g i
  proof: congr_arg _ funext h

@[to_dual]

中文:
定理 iSup_congr
  条件: (h : 对任意 i, f i = g i)
  结论: ⨆ i, f i = ⨆ i, g i
  证明: congr_arg _ funext h

@[to_dual]

Depends on / 依赖: congr_arg
-/
theorem iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i :=
congr_arg _ funext h

@[to_dual]
/--
theorem `biSup_congr` / 定理 `biSup_congr`

English:
theorem biSup_congr
  given: {p : ι -> Prop} (h : forall i, p i -> f i = g i)
  proof: iSup_congr fun i => iSup_congr (h i)

@[to_dual]

中文:
定理 biSup_congr
  条件: {p : ι -> 命题} (h : 对任意 i, p i -> f i = g i)
  证明: iSup_congr fun i => iSup_congr (h i)

@[to_dual]

Depends on / 依赖: iSup_congr
-/
theorem biSup_congr {p : ι -> Prop} (h : forall i, p i -> f i = g i) :
    ⨆ (i) (_ : p i), f i = ⨆ (i) (_ : p i), g i :=
  iSup_congr fun i => iSup_congr (h i)

@[to_dual]
/--
theorem `biSup_congr'` / 定理 `biSup_congr'`

English:
theorem biSup_congr'
  statement: {p : ι -> Prop} {f g : (i : ι) -> p i -> α}
  proof: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization w

中文:
定理 biSup_congr'
  结论: {p : ι -> 命题} {f g : (i : ι) -> p i -> α}
  证明: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization w

Depends on / 依赖: Before, Mathlib, adaptation_note, canonicalizer, closed, directed, github, github.com, leanprover, minimization, normalizer, original, problem, replacing, whether
-/
theorem biSup_congr' {p : ι -> Prop} {f g : (i : ι) -> p i -> α}
    (h : forall i (hi : p i), f i hi = g i hi) :
    ⨆ i, ⨆ (hi : p i), f i hi = ⨆ i, ⨆ (hi : p i), g i hi := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  simp_all

@[to_dual]
/--
theorem `Function.Surjective.iSup_comp` / 定理 `Function.Surjective.iSup_comp`

English:
theorem Function.Surjective.iSup_comp
  given: {f : ι -> ι'} (hf : Surjective f) (g : ι' -> α)
  proof: by
  simp only [iSup.eq_1]
  congr
  exact hf.range_comp g

@[to_dual]

中文:
定理 Function.Surjective.iSup_comp
  条件: {f : ι -> ι'} (hf : Surjective f) (g : ι' -> α)
  证明: by
  simp only [iSup.eq_1]
  congr
  exact hf.range_comp g

@[to_dual]

Depends on / 依赖: eq_1, hf.range_comp, iSup.eq_1, range_comp
-/
theorem Function.Surjective.iSup_comp {f : ι -> ι'} (hf : Surjective f) (g : ι' -> α) :
    ⨆ x, g (f x) = ⨆ y, g y := by
  simp only [iSup.eq_1]
  congr
  exact hf.range_comp g

@[to_dual]
/--
theorem `Equiv.iSup_comp` / 定理 `Equiv.iSup_comp`

English:
theorem Equiv.iSup_comp
  given: {g : ι' -> α} (e : ι ≃ ι')
  statement: ⨆ x, g (e x) = ⨆ y, g y
  proof: e.surjective.iSup_comp _

@[to_dual]

中文:
定理 Equiv.iSup_comp
  条件: {g : ι' -> α} (e : ι ≃ ι')
  结论: ⨆ x, g (e x) = ⨆ y, g y
  证明: e.surjective.iSup_comp _

@[to_dual]

Depends on / 依赖: e.surjective.iSup_comp, iSup_comp, surjective
-/
theorem Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e x) = ⨆ y, g y :=
  e.surjective.iSup_comp _

@[to_dual]
/--
theorem `Function.Surjective.iSup_congr` / 定理 `Function.Surjective.iSup_congr`

English:
theorem Function.Surjective.iSup_congr
  statement: {g : ι' -> α} (h : ι -> ι') (h1 : Surjective h)
  proof: by
  convert! h1.iSup_comp g
  exact (h2 _).symm

@[to_dual]

中文:
定理 Function.Surjective.iSup_congr
  结论: {g : ι' -> α} (h : ι -> ι') (h1 : Surjective h)
  证明: by
  convert! h1.iSup_comp g
  exact (h2 _).symm

@[to_dual]
-/
protected theorem Function.Surjective.iSup_congr {g : ι' -> α} (h : ι -> ι') (h1 : Surjective h)
    (h2 : forall x, g (h x) = f x) : ⨆ x, f x = ⨆ y, g y := by
  convert! h1.iSup_comp g
  exact (h2 _).symm

@[to_dual]
/--
theorem `Equiv.iSup_congr` / 定理 `Equiv.iSup_congr`

English:
theorem Equiv.iSup_congr
  given: {g : ι' -> α} (e : ι ≃ ι') (h : forall x, g (e x) = f x)
  proof: e.surjective.iSup_congr _ h

@[to_dual (attr := congr)]

中文:
定理 Equiv.iSup_congr
  条件: {g : ι' -> α} (e : ι ≃ ι') (h : 对任意 x, g (e x) = f x)
  证明: e.surjective.iSup_congr _ h

@[to_dual (attr := congr)]
-/
protected theorem Equiv.iSup_congr {g : ι' -> α} (e : ι ≃ ι') (h : forall x, g (e x) = f x) :
    ⨆ x, f x = ⨆ y, g y :=
  e.surjective.iSup_congr _ h

@[to_dual (attr := congr)]
/--
theorem `iSup_congr_Prop` / 定理 `iSup_congr_Prop`

English:
theorem iSup_congr_Prop
  statement: {p q : Prop} {f₁ : p -> α} {f₂ : q -> α} (pq : p ↔ q)
  proof: by
  obtain rfl := propext pq
  congr with x
  apply f

@[to_dual]

中文:
定理 iSup_congr_Prop
  结论: {p q : 命题} {f₁ : p -> α} {f₂ : q -> α} (pq : p ↔ q)
  证明: by
  obtain rfl := propext pq
  congr with x
  apply f

@[to_dual]

Depends on / 依赖: propext
-/
theorem iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α} (pq : p ↔ q)
    (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂ := by
  obtain rfl := propext pq
  congr with x
  apply f

@[to_dual]
/--
theorem `iSup_plift_up` / 定理 `iSup_plift_up`

English:
theorem iSup_plift_up
  given: (f : PLift ι -> α)
  statement: ⨆ i, f (PLift.up i) = ⨆ i, f i
  proof: (PLift.up_surjective.iSup_congr _) fun _ => rfl

@[to_dual]

中文:
定理 iSup_plift_up
  条件: (f : PLift ι -> α)
  结论: ⨆ i, f (PLift.up i) = ⨆ i, f i
  证明: (PLift.up_surjective.iSup_congr _) fun _ => rfl

@[to_dual]

Depends on / 依赖: PLift.up_surjective.iSup_congr, iSup_congr, up_surjective
-/
theorem iSup_plift_up (f : PLift ι -> α) : ⨆ i, f (PLift.up i) = ⨆ i, f i :=
  (PLift.up_surjective.iSup_congr _) fun _ => rfl

@[to_dual]
/--
theorem `iSup_plift_down` / 定理 `iSup_plift_down`

English:
theorem iSup_plift_down
  given: (f : ι -> α)
  statement: ⨆ i, f (PLift.down i) = ⨆ i, f i
  proof: (PLift.down_surjective.iSup_congr _) fun _ => rfl

@[to_dual]

中文:
定理 iSup_plift_down
  条件: (f : ι -> α)
  结论: ⨆ i, f (PLift.down i) = ⨆ i, f i
  证明: (PLift.down_surjective.iSup_congr _) fun _ => rfl

@[to_dual]

Depends on / 依赖: PLift.down_surjective.iSup_congr, down_surjective, iSup_congr
-/
theorem iSup_plift_down (f : ι -> α) : ⨆ i, f (PLift.down i) = ⨆ i, f i :=
  (PLift.down_surjective.iSup_congr _) fun _ => rfl

@[to_dual]
/--
theorem `iSup_range'` / 定理 `iSup_range'`

English:
theorem iSup_range'
  given: (g : β -> α) (f : ι -> β)
  statement: ⨆ b : range f, g b = ⨆ i, g (f i)
  proof: by
  rw [iSup]; rw [iSup]; rw [← image_eq_range]; rw [← range_comp']

@[to_dual]

中文:
定理 iSup_range'
  条件: (g : β -> α) (f : ι -> β)
  结论: ⨆ b : range f, g b = ⨆ i, g (f i)
  证明: by
  rw [iSup]; rw [iSup]; rw [← image_eq_range]; rw [← range_comp']

@[to_dual]

Depends on / 依赖: image_eq_range, range_comp
-/
theorem iSup_range' (g : β -> α) (f : ι -> β) : ⨆ b : range f, g b = ⨆ i, g (f i) := by
  rw [iSup]; rw [iSup]; rw [← image_eq_range]; rw [← range_comp']

@[to_dual]
/--
theorem `sSup_image'` / 定理 `sSup_image'`

English:
theorem sSup_image'
  given: {s : Set β} {f : β -> α}
  statement: sSup (f '' s) = ⨆ a : s, f a
  proof: by
  rw [iSup]; rw [image_eq_range]

中文:
定理 sSup_image'
  条件: {s : Set β} {f : β -> α}
  结论: sSup (f '' s) = ⨆ a : s, f a
  证明: by
  rw [iSup]; rw [image_eq_range]

Depends on / 依赖: image_eq_range
-/
theorem sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a : s, f a := by
  rw [iSup]; rw [image_eq_range]

end SupSet

section

variable [CompleteLattice α] {f g s : ι -> α} {a b : α}

@[to_dual iInf_le]
/--
theorem `le_iSup` / 定理 `le_iSup`

English:
theorem le_iSup
  given: (f : ι -> α) (i : ι)
  statement: f i <= iSup f
  proof: le_sSup ⟨i, rfl⟩

中文:
定理 le_iSup
  条件: (f : ι -> α) (i : ι)
  结论: f i <= iSup f
  证明: le_sSup ⟨i, rfl⟩

Depends on / 依赖: le_sSup
-/
theorem le_iSup (f : ι -> α) (i : ι) : f i <= iSup f :=
  le_sSup ⟨i, rfl⟩

/--
lemma `iInf_le_iSup` / 引理 `iInf_le_iSup`

English:
lemma iInf_le_iSup
  given: [Nonempty ι]
  statement: ⨅ i, f i <= ⨆ i, f i
  proof: (iInf_le _ (Classical.arbitrary _)).trans le_iSup _ (Classical.arbitrary _)

@[to_dual]

中文:
引理 iInf_le_iSup
  条件: [Nonempty ι]
  结论: ⨅ i, f i <= ⨆ i, f i
  证明: (iInf_le _ (Classical.arbitrary _)).trans le_iSup _ (Classical.arbitrary _)

@[to_dual]

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, iInf_le, le_iSup
-/
lemma iInf_le_iSup [Nonempty ι] : ⨅ i, f i <= ⨆ i, f i :=
(iInf_le _ (Classical.arbitrary _)).trans le_iSup _ (Classical.arbitrary _)

@[to_dual]
/--
theorem `isLUB_iSup` / 定理 `isLUB_iSup`

English:
theorem isLUB_iSup
  statement: IsLUB (range f) (⨆ j, f j)
  proof: isLUB_sSup _

@[to_dual]

中文:
定理 isLUB_iSup
  结论: IsLUB (range f) (⨆ j, f j)
  证明: isLUB_sSup _

@[to_dual]

Depends on / 依赖: isLUB_sSup
-/
theorem isLUB_iSup : IsLUB (range f) (⨆ j, f j) :=
  isLUB_sSup _

@[to_dual]
/--
theorem `IsLUB.iSup_eq` / 定理 `IsLUB.iSup_eq`

English:
theorem IsLUB.iSup_eq
  given: (h : IsLUB (range f) a)
  statement: ⨆ j, f j = a
  proof: h.sSup_eq

@[to_dual iInf_le_of_le]

中文:
定理 IsLUB.iSup_eq
  条件: (h : IsLUB (range f) a)
  结论: ⨆ j, f j = a
  证明: h.sSup_eq

@[to_dual iInf_le_of_le]

Depends on / 依赖: h.sSup_eq, sSup_eq
-/
theorem IsLUB.iSup_eq (h : IsLUB (range f) a) : ⨆ j, f j = a :=
  h.sSup_eq

@[to_dual iInf_le_of_le]
/--
theorem `le_iSup_of_le` / 定理 `le_iSup_of_le`

English:
theorem le_iSup_of_le
  given: (i : ι) (h : a <= f i)
  statement: a <= iSup f
  proof: h.trans le_iSup _ i

@[to_dual iInf₂_le]

中文:
定理 le_iSup_of_le
  条件: (i : ι) (h : a <= f i)
  结论: a <= iSup f
  证明: h.trans le_iSup _ i

@[to_dual iInf₂_le]

Depends on / 依赖: h.trans, le_iSup
-/
theorem le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f :=
h.trans le_iSup _ i

@[to_dual iInf₂_le]
/--
theorem `le_iSup₂` / 定理 `le_iSup₂`

English:
theorem le_iSup₂
  given: {f : forall i, κ i -> α} (i : ι) (j : κ i)
  statement: f i j <= ⨆ (i) (j), f i j
  proof: le_iSup_of_le i le_iSup (f i) j

@[to_dual iInf₂_le_of_le]

中文:
定理 le_iSup₂
  条件: {f : 对任意 i, κ i -> α} (i : ι) (j : κ i)
  结论: f i j <= ⨆ (i) (j), f i j
  证明: le_iSup_of_le i le_iSup (f i) j

@[to_dual iInf₂_le_of_le]

Depends on / 依赖: le_iSup, le_iSup_of_le
-/
theorem le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <= ⨆ (i) (j), f i j :=
le_iSup_of_le i le_iSup (f i) j

@[to_dual iInf₂_le_of_le]
/--
theorem `le_iSup₂_of_le` / 定理 `le_iSup₂_of_le`

English:
theorem le_iSup₂_of_le
  given: {f : forall i, κ i -> α} (i : ι) (j : κ i) (h : a <= f i j)
  proof: h.trans le_iSup₂ i j

@[to_dual le_iInf]

中文:
定理 le_iSup₂_of_le
  条件: {f : 对任意 i, κ i -> α} (i : ι) (j : κ i) (h : a <= f i j)
  证明: h.trans le_iSup₂ i j

@[to_dual le_iInf]

Depends on / 依赖: h.trans
-/
theorem le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i) (h : a <= f i j) :
    a <= ⨆ (i) (j), f i j :=
h.trans le_iSup₂ i j

@[to_dual le_iInf]
/--
theorem `iSup_le` / 定理 `iSup_le`

English:
theorem iSup_le
  given: (h : forall i, f i <= a)
  statement: iSup f <= a
  proof: sSup_le fun _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual le_iInf₂]

中文:
定理 iSup_le
  条件: (h : 对任意 i, f i <= a)
  结论: iSup f <= a
  证明: sSup_le fun _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual le_iInf₂]

Depends on / 依赖: sSup_le
-/
theorem iSup_le (h : forall i, f i <= a) : iSup f <= a :=
  sSup_le fun _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual le_iInf₂]
/--
theorem `iSup₂_le` / 定理 `iSup₂_le`

English:
theorem iSup₂_le
  given: {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
  statement: ⨆ (i) (j), f i j <= a
  proof: iSup_le fun i => iSup_le h i

@[to_dual iInf_le_iInf₂]

中文:
定理 iSup₂_le
  条件: {f : 对任意 i, κ i -> α} (h : 对任意 i j, f i j <= a)
  结论: ⨆ (i) (j), f i j <= a
  证明: iSup_le fun i => iSup_le h i

@[to_dual iInf_le_iInf₂]

Depends on / 依赖: iSup_le
-/
theorem iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a) : ⨆ (i) (j), f i j <= a :=
iSup_le fun i => iSup_le h i

@[to_dual iInf_le_iInf₂]
/--
theorem `iSup₂_le_iSup` / 定理 `iSup₂_le_iSup`

English:
theorem iSup₂_le_iSup
  given: (κ : ι -> Sort*) (f : ι -> α)
  statement: ⨆ (i) (_ : κ i), f i <= ⨆ i, f i
  proof: iSup₂_le fun i _ => le_iSup f i

@[to_dual (attr := gcongr)]

中文:
定理 iSup₂_le_iSup
  条件: (κ : ι -> Sort*) (f : ι -> α)
  结论: ⨆ (i) (_ : κ i), f i <= ⨆ i, f i
  证明: iSup₂_le fun i _ => le_iSup f i

@[to_dual (attr := gcongr)]

Depends on / 依赖: le_iSup
-/
theorem iSup₂_le_iSup (κ : ι -> Sort*) (f : ι -> α) : ⨆ (i) (_ : κ i), f i <= ⨆ i, f i :=
  iSup₂_le fun i _ => le_iSup f i

@[to_dual (attr := gcongr)]
/--
theorem `iSup_mono` / 定理 `iSup_mono`

English:
theorem iSup_mono
  given: (h : forall i, f i <= g i)
  statement: iSup f <= iSup g
  proof: iSup_le fun i => le_iSup_of_le i h i

@[to_dual]

中文:
定理 iSup_mono
  条件: (h : 对任意 i, f i <= g i)
  结论: iSup f <= iSup g
  证明: iSup_le fun i => le_iSup_of_le i h i

@[to_dual]

Depends on / 依赖: iSup_le, le_iSup_of_le
-/
theorem iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g :=
iSup_le fun i => le_iSup_of_le i h i

@[to_dual]
/--
theorem `iSup₂_mono` / 定理 `iSup₂_mono`

English:
theorem iSup₂_mono
  given: {f g : forall i, κ i -> α} (h : forall i j, f i j <= g i j)
  proof: iSup_mono fun i => iSup_mono h i

@[to_dual]

中文:
定理 iSup₂_mono
  条件: {f g : 对任意 i, κ i -> α} (h : 对任意 i j, f i j <= g i j)
  证明: iSup_mono fun i => iSup_mono h i

@[to_dual]

Depends on / 依赖: iSup_mono
-/
theorem iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j <= g i j) :
    ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j :=
iSup_mono fun i => iSup_mono h i

@[to_dual]
/--
theorem `iSup_mono'` / 定理 `iSup_mono'`

English:
theorem iSup_mono'
  given: {g : ι' -> α} (h : forall i, exists i', f i <= g i')
  statement: iSup f <= iSup g
  proof: iSup_le fun i => Exists.elim (h i) le_iSup_of_le

@[to_dual]

中文:
定理 iSup_mono'
  条件: {g : ι' -> α} (h : 对任意 i, 存在 i', f i <= g i')
  结论: iSup f <= iSup g
  证明: iSup_le fun i => Exists.elim (h i) le_iSup_of_le

@[to_dual]

Depends on / 依赖: Exists, Exists.elim, iSup_le, le_iSup_of_le
-/
theorem iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g i') : iSup f <= iSup g :=
  iSup_le fun i => Exists.elim (h i) le_iSup_of_le

@[to_dual]
/--
theorem `iSup₂_mono'` / 定理 `iSup₂_mono'`

English:
theorem iSup₂_mono'
  given: {f : forall i, κ i -> α} {g : forall i', κ' i' -> α} (h : forall i j, exists i' j', f i j <= g i' j')
  proof: iSup₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_iSup₂_of_le i' j' h

@[to_dual]

中文:
定理 iSup₂_mono'
  条件: {f : 对任意 i, κ i -> α} {g : 对任意 i', κ' i' -> α} (h : 对任意 i j, 存在 i' j', f i j <= g i' j')
  证明: iSup₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_iSup₂_of_le i' j' h

@[to_dual]
-/
theorem iSup₂_mono' {f : forall i, κ i -> α} {g : forall i', κ' i' -> α} (h : forall i j, exists i' j', f i j <= g i' j') :
    ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j :=
  iSup₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_iSup₂_of_le i' j' h

@[to_dual]
/--
theorem `iSup_const_mono` / 定理 `iSup_const_mono`

English:
theorem iSup_const_mono
  given: (h : ι -> ι')
  statement: ⨆ _ : ι, a <= ⨆ _ : ι', a
  proof: iSup_le le_iSup _ ∘ h

@[to_dual none]

中文:
定理 iSup_const_mono
  条件: (h : ι -> ι')
  结论: ⨆ _ : ι, a <= ⨆ _ : ι', a
  证明: iSup_le le_iSup _ ∘ h

@[to_dual none]

Depends on / 依赖: iSup_le, le_iSup
-/
theorem iSup_const_mono (h : ι -> ι') : ⨆ _ : ι, a <= ⨆ _ : ι', a :=
iSup_le le_iSup _ ∘ h

@[to_dual none]
/--
theorem `iSup_iInf_le_iInf_iSup` / 定理 `iSup_iInf_le_iInf_iSup`

English:
theorem iSup_iInf_le_iInf_iSup
  given: (f : ι -> ι' -> α)
  statement: ⨆ i, ⨅ j, f i j <= ⨅ j, ⨆ i, f i j
  proof: iSup_le fun i => iInf_mono fun j => le_iSup (fun i => f i j) i

@[to_dual]

中文:
定理 iSup_iInf_le_iInf_iSup
  条件: (f : ι -> ι' -> α)
  结论: ⨆ i, ⨅ j, f i j <= ⨅ j, ⨆ i, f i j
  证明: iSup_le fun i => iInf_mono fun j => le_iSup (fun i => f i j) i

@[to_dual]

Depends on / 依赖: iInf_mono, iSup_le, le_iSup
-/
theorem iSup_iInf_le_iInf_iSup (f : ι -> ι' -> α) : ⨆ i, ⨅ j, f i j <= ⨅ j, ⨆ i, f i j :=
  iSup_le fun i => iInf_mono fun j => le_iSup (fun i => f i j) i

@[to_dual]
/--
theorem `biSup_mono` / 定理 `biSup_mono`

English:
theorem biSup_mono
  given: {p q : ι -> Prop} (hpq : forall i, p i -> q i)
  proof: iSup_mono fun i => iSup_const_mono (hpq i)

@[to_dual (attr := simp) le_iInf_iff]

中文:
定理 biSup_mono
  条件: {p q : ι -> 命题} (hpq : 对任意 i, p i -> q i)
  证明: iSup_mono fun i => iSup_const_mono (hpq i)

@[to_dual (attr := simp) le_iInf_iff]

Depends on / 依赖: iSup_const_mono, iSup_mono
-/
theorem biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) :
    ⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i :=
  iSup_mono fun i => iSup_const_mono (hpq i)

@[to_dual (attr := simp) le_iInf_iff]
/--
theorem `iSup_le_iff` / 定理 `iSup_le_iff`

English:
theorem iSup_le_iff
  statement: iSup f <= a ↔ forall i, f i <= a
  proof: (isLUB_le_iff isLUB_iSup).trans forall_mem_range

@[to_dual le_iInf₂_iff]

中文:
定理 iSup_le_iff
  结论: iSup f <= a ↔ 对任意 i, f i <= a
  证明: (isLUB_le_iff isLUB_iSup).trans forall_mem_range

@[to_dual le_iInf₂_iff]

Depends on / 依赖: forall_mem_range, isLUB_iSup, isLUB_le_iff
-/
theorem iSup_le_iff : iSup f <= a ↔ forall i, f i <= a :=
  (isLUB_le_iff isLUB_iSup).trans forall_mem_range

@[to_dual le_iInf₂_iff]
/--
theorem `iSup₂_le_iff` / 定理 `iSup₂_le_iff`

English:
theorem iSup₂_le_iff
  given: {f : forall i, κ i -> α}
  statement: ⨆ (i) (j), f i j <= a ↔ forall i j, f i j <= a
  proof: by
  simp_rw [iSup_le_iff]

@[to_dual]

中文:
定理 iSup₂_le_iff
  条件: {f : 对任意 i, κ i -> α}
  结论: ⨆ (i) (j), f i j <= a ↔ 对任意 i j, f i j <= a
  证明: by
  simp_rw [iSup_le_iff]

@[to_dual]

Depends on / 依赖: iSup_le_iff, simp_rw
-/
theorem iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <= a ↔ forall i j, f i j <= a := by
  simp_rw [iSup_le_iff]

@[to_dual]
/--
theorem `sSup_eq_iSup` / 定理 `sSup_eq_iSup`

English:
theorem sSup_eq_iSup
  given: {s : Set α}
  statement: sSup s = ⨆ a in s, a
  proof: le_antisymm (sSup_le le_iSup₂) (iSup₂_le fun _ => le_sSup)

@[to_dual]

中文:
定理 sSup_eq_iSup
  条件: {s : Set α}
  结论: sSup s = ⨆ a in s, a
  证明: le_antisymm (sSup_le le_iSup₂) (iSup₂_le fun _ => le_sSup)

@[to_dual]

Depends on / 依赖: le_antisymm, le_sSup, sSup_le
-/
theorem sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a :=
  le_antisymm (sSup_le le_iSup₂) (iSup₂_le fun _ => le_sSup)

@[to_dual]
/--
lemma `sSup_lowerBounds_eq_sInf` / 引理 `sSup_lowerBounds_eq_sInf`

English:
lemma sSup_lowerBounds_eq_sInf
  given: (s : Set α)
  statement: sSup (lowerBounds s) = sInf s
  proof: (isLUB_sSup _).unique (isGLB_sInf _).isLUB

@[deprecated (since := "2026-02-01")] alias sInf_upperBounds_eq_csSup := sInf_upperBounds_eq_sSup

@[to_dual map_iInf_le]

中文:
引理 sSup_lowerBounds_eq_sInf
  条件: (s : Set α)
  结论: sSup (lowerBounds s) = sInf s
  证明: (isLUB_sSup _).unique (isGLB_sInf _).isLUB

@[deprecated (since := "2026-02-01")] alias sInf_upperBounds_eq_csSup := sInf_upperBounds_eq_sSup

@[to_dual map_iInf_le]

Depends on / 依赖: isGLB_sInf, isLUB_sSup, unique
-/
lemma sSup_lowerBounds_eq_sInf (s : Set α) : sSup (lowerBounds s) = sInf s :=
  (isLUB_sSup _).unique (isGLB_sInf _).isLUB

@[deprecated (since := "2026-02-01")] alias sInf_upperBounds_eq_csSup := sInf_upperBounds_eq_sSup

@[to_dual map_iInf_le]
/--
theorem `Monotone.le_map_iSup` / 定理 `Monotone.le_map_iSup`

English:
theorem Monotone.le_map_iSup
  given: [CompleteLattice β] {f : α -> β} (hf : Monotone f)
  proof: iSup_le fun _ => hf le_iSup _ _

@[to_dual map_iSup_le]

中文:
定理 Monotone.le_map_iSup
  条件: [CompleteLattice β] {f : α -> β} (hf : Monotone f)
  证明: iSup_le fun _ => hf le_iSup _ _

@[to_dual map_iSup_le]

Depends on / 依赖: iSup_le, le_iSup
-/
theorem Monotone.le_map_iSup [CompleteLattice β] {f : α -> β} (hf : Monotone f) :
    ⨆ i, f (s i) <= f (iSup s) :=
iSup_le fun _ => hf le_iSup _ _

@[to_dual map_iSup_le]
/--
theorem `Antitone.le_map_iInf` / 定理 `Antitone.le_map_iInf`

English:
theorem Antitone.le_map_iInf
  given: [CompleteLattice β] {f : α -> β} (hf : Antitone f)
  proof: hf.dual_left.le_map_iSup

@[to_dual map_iInf₂_le]

中文:
定理 Antitone.le_map_iInf
  条件: [CompleteLattice β] {f : α -> β} (hf : Antitone f)
  证明: hf.dual_left.le_map_iSup

@[to_dual map_iInf₂_le]

Depends on / 依赖: dual_left, hf.dual_left.le_map_iSup, le_map_iSup
-/
theorem Antitone.le_map_iInf [CompleteLattice β] {f : α -> β} (hf : Antitone f) :
    ⨆ i, f (s i) <= f (iInf s) :=
  hf.dual_left.le_map_iSup

@[to_dual map_iInf₂_le]
/--
theorem `Monotone.le_map_iSup₂` / 定理 `Monotone.le_map_iSup₂`

English:
theorem Monotone.le_map_iSup₂
  given: [CompleteLattice β] {f : α -> β} (hf : Monotone f) (s : forall i, κ i -> α)
  proof: iSup₂_le fun _ _ => hf le_iSup₂ _ _

@[to_dual map_iSup₂_le]

中文:
定理 Monotone.le_map_iSup₂
  条件: [CompleteLattice β] {f : α -> β} (hf : Monotone f) (s : 对任意 i, κ i -> α)
  证明: iSup₂_le fun _ _ => hf le_iSup₂ _ _

@[to_dual map_iSup₂_le]
-/
theorem Monotone.le_map_iSup₂ [CompleteLattice β] {f : α -> β} (hf : Monotone f) (s : forall i, κ i -> α) :
    ⨆ (i) (j), f (s i j) <= f (⨆ (i) (j), s i j) :=
iSup₂_le fun _ _ => hf le_iSup₂ _ _

@[to_dual map_iSup₂_le]
/--
theorem `Antitone.le_map_iInf₂` / 定理 `Antitone.le_map_iInf₂`

English:
theorem Antitone.le_map_iInf₂
  given: [CompleteLattice β] {f : α -> β} (hf : Antitone f) (s : forall i, κ i -> α)
  proof: hf.dual_left.le_map_iSup₂ _

@[to_dual map_sInf_le]

中文:
定理 Antitone.le_map_iInf₂
  条件: [CompleteLattice β] {f : α -> β} (hf : Antitone f) (s : 对任意 i, κ i -> α)
  证明: hf.dual_left.le_map_iSup₂ _

@[to_dual map_sInf_le]

Depends on / 依赖: dual_left, hf.dual_left.le_map_iSup
-/
theorem Antitone.le_map_iInf₂ [CompleteLattice β] {f : α -> β} (hf : Antitone f) (s : forall i, κ i -> α) :
    ⨆ (i) (j), f (s i j) <= f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_iSup₂ _

@[to_dual map_sInf_le]
/--
theorem `Monotone.le_map_sSup` / 定理 `Monotone.le_map_sSup`

English:
theorem Monotone.le_map_sSup
  given: [CompleteLattice β] {s : Set α} {f : α -> β} (hf : Monotone f)
  proof: by rw [sSup_eq_iSup]; exact hf.le_map_iSup₂ _

@[to_dual map_sSup_le]

中文:
定理 Monotone.le_map_sSup
  条件: [CompleteLattice β] {s : Set α} {f : α -> β} (hf : Monotone f)
  证明: by rw [sSup_eq_iSup]; exact hf.le_map_iSup₂ _

@[to_dual map_sSup_le]

Depends on / 依赖: hf.le_map_iSup, sSup_eq_iSup
-/
theorem Monotone.le_map_sSup [CompleteLattice β] {s : Set α} {f : α -> β} (hf : Monotone f) :
    ⨆ a in s, f a <= f (sSup s) := by rw [sSup_eq_iSup]; exact hf.le_map_iSup₂ _

@[to_dual map_sSup_le]
/--
theorem `Antitone.le_map_sInf` / 定理 `Antitone.le_map_sInf`

English:
theorem Antitone.le_map_sInf
  given: [CompleteLattice β] {s : Set α} {f : α -> β} (hf : Antitone f)
  proof: hf.dual_left.le_map_sSup

@[to_dual]

中文:
定理 Antitone.le_map_sInf
  条件: [CompleteLattice β] {s : Set α} {f : α -> β} (hf : Antitone f)
  证明: hf.dual_left.le_map_sSup

@[to_dual]

Depends on / 依赖: dual_left, hf.dual_left.le_map_sSup, le_map_sSup
-/
theorem Antitone.le_map_sInf [CompleteLattice β] {s : Set α} {f : α -> β} (hf : Antitone f) :
    ⨆ a in s, f a <= f (sInf s) :=
  hf.dual_left.le_map_sSup

@[to_dual]
/--
theorem `OrderIso.map_iSup` / 定理 `OrderIso.map_iSup`

English:
theorem OrderIso.map_iSup
  given: [CompleteLattice β] (f : α ≃o β) (x : ι -> α)
  proof: eq_of_forall_ge_iff f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]

中文:
定理 OrderIso.map_iSup
  条件: [CompleteLattice β] (f : α ≃o β) (x : ι -> α)
  证明: eq_of_forall_ge_iff f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]

Depends on / 依赖: eq_of_forall_ge_iff, f.le_iff_le, f.surjective.forall, iSup_le_iff, le_iff_le, surjective
-/
theorem OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x : ι -> α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
eq_of_forall_ge_iff f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]
/--
lemma `OrderIso.map_iSup₂` / 引理 `OrderIso.map_iSup₂`

English:
lemma OrderIso.map_iSup₂
  given: [CompleteLattice β] (f : α ≃o β) (x : forall i, κ i -> α)
  proof: eq_of_forall_ge_iff f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]

中文:
引理 OrderIso.map_iSup₂
  条件: [CompleteLattice β] (f : α ≃o β) (x : 对任意 i, κ i -> α)
  证明: eq_of_forall_ge_iff f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]

Depends on / 依赖: eq_of_forall_ge_iff, f.le_iff_le, f.surjective.forall, iSup_le_iff, le_iff_le, surjective
-/
lemma OrderIso.map_iSup₂ [CompleteLattice β] (f : α ≃o β) (x : forall i, κ i -> α) :
    f (⨆ i, ⨆ j, x i j) = ⨆ i, ⨆ j, f (x i j) :=
eq_of_forall_ge_iff f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

@[to_dual]
/--
theorem `OrderIso.map_sSup` / 定理 `OrderIso.map_sSup`

English:
theorem OrderIso.map_sSup
  given: [CompleteLattice β] (f : α ≃o β) (s : Set α)
  proof: by
  simp only [sSup_eq_iSup, OrderIso.map_iSup]

@[to_dual le_iInf_comp]

中文:
定理 OrderIso.map_sSup
  条件: [CompleteLattice β] (f : α ≃o β) (s : Set α)
  证明: by
  simp only [sSup_eq_iSup, OrderIso.map_iSup]

@[to_dual le_iInf_comp]

Depends on / 依赖: OrderIso, OrderIso.map_iSup, map_iSup, sSup_eq_iSup
-/
theorem OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = ⨆ a in s, f a := by
  simp only [sSup_eq_iSup, OrderIso.map_iSup]

@[to_dual le_iInf_comp]
/--
theorem `iSup_comp_le` / 定理 `iSup_comp_le`

English:
theorem iSup_comp_le
  given: {ι' : Sort*} (f : ι' -> α) (g : ι -> ι')
  statement: ⨆ x, f (g x) <= ⨆ y, f y
  proof: iSup_mono' fun _ => ⟨_, le_rfl⟩

@[to_dual]

中文:
定理 iSup_comp_le
  条件: {ι' : Sort*} (f : ι' -> α) (g : ι -> ι')
  结论: ⨆ x, f (g x) <= ⨆ y, f y
  证明: iSup_mono' fun _ => ⟨_, le_rfl⟩

@[to_dual]

Depends on / 依赖: iSup_mono, le_rfl
-/
theorem iSup_comp_le {ι' : Sort*} (f : ι' -> α) (g : ι -> ι') : ⨆ x, f (g x) <= ⨆ y, f y :=
  iSup_mono' fun _ => ⟨_, le_rfl⟩

@[to_dual]
/--
theorem `Monotone.iSup_comp_eq` / 定理 `Monotone.iSup_comp_eq`

English:
theorem Monotone.iSup_comp_eq
  statement: [Preorder β] {f : β -> α} (hf : Monotone f) {s : ι -> β}
  proof: le_antisymm (iSup_comp_le _ _) (iSup_mono' fun x => (hs x).imp fun _ hi => hf hi)

@[to_dual le_iInf_const]

中文:
定理 Monotone.iSup_comp_eq
  结论: [Preorder β] {f : β -> α} (hf : Monotone f) {s : ι -> β}
  证明: le_antisymm (iSup_comp_le _ _) (iSup_mono' fun x => (hs x).imp fun _ hi => hf hi)

@[to_dual le_iInf_const]

Depends on / 依赖: iSup_comp_le, iSup_mono, le_antisymm
-/
theorem Monotone.iSup_comp_eq [Preorder β] {f : β -> α} (hf : Monotone f) {s : ι -> β}
    (hs : forall x, exists i, x <= s i) : ⨆ x, f (s x) = ⨆ y, f y :=
  le_antisymm (iSup_comp_le _ _) (iSup_mono' fun x => (hs x).imp fun _ hi => hf hi)

@[to_dual le_iInf_const]
/--
theorem `iSup_const_le` / 定理 `iSup_const_le`

English:
theorem iSup_const_le
  statement: ⨆ _ : ι, a <= a
  proof: iSup_le fun _ => le_rfl

中文:
定理 iSup_const_le
  结论: ⨆ _ : ι, a <= a
  证明: iSup_le fun _ => le_rfl

Depends on / 依赖: iSup_le, le_rfl
-/
theorem iSup_const_le : ⨆ _ : ι, a <= a :=
  iSup_le fun _ => le_rfl

-- We generalize this to conditionally complete lattices in `ciSup_const` and `ciInf_const`.
@[to_dual]
/--
theorem `iSup_const` / 定理 `iSup_const`

English:
theorem iSup_const
  given: [Nonempty ι]
  statement: ⨆ _ : ι, a = a
  proof: by rw [iSup, range_const, sSup_singleton]

@[to_dual]

中文:
定理 iSup_const
  条件: [Nonempty ι]
  结论: ⨆ _ : ι, a = a
  证明: by rw [iSup, range_const, sSup_singleton]

@[to_dual]

Depends on / 依赖: range_const, sSup_singleton
-/
theorem iSup_const [Nonempty ι] : ⨆ _ : ι, a = a := by rw [iSup, range_const, sSup_singleton]

@[to_dual]
/--
lemma `iSup_unique` / 引理 `iSup_unique`

English:
lemma iSup_unique
  given: [Unique ι] (f : ι -> α)
  statement: ⨆ i, f i = f default
  proof: by
  simp only [congr_arg f (Unique.eq_default _), iSup_const]

@[to_dual (attr := simp)]

中文:
引理 iSup_unique
  条件: [Unique ι] (f : ι -> α)
  结论: ⨆ i, f i = f default
  证明: by
  simp only [congr_arg f (Unique.eq_default _), iSup_const]

@[to_dual (attr := simp)]

Depends on / 依赖: Unique, Unique.eq_default, congr_arg, eq_default, iSup_const
-/
lemma iSup_unique [Unique ι] (f : ι -> α) : ⨆ i, f i = f default := by
  simp only [congr_arg f (Unique.eq_default _), iSup_const]

@[to_dual (attr := simp)]
/--
theorem `iSup_bot` / 定理 `iSup_bot`

English:
theorem iSup_bot
  statement: (⨆ _ : ι, ⊥ : α) = ⊥
  proof: bot_unique iSup_const_le

@[to_dual (attr := simp)]

中文:
定理 iSup_bot
  结论: (⨆ _ : ι, ⊥ : α) = ⊥
  证明: bot_unique iSup_const_le

@[to_dual (attr := simp)]

Depends on / 依赖: bot_unique, iSup_const_le
-/
theorem iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥ :=
  bot_unique iSup_const_le

@[to_dual (attr := simp)]
/--
theorem `iSup_eq_bot` / 定理 `iSup_eq_bot`

English:
theorem iSup_eq_bot
  statement: iSup s = ⊥ ↔ forall i, s i = ⊥
  proof: sSup_eq_bot.trans forall_mem_range

@[to_dual (attr := simp) iInf_lt_top]

中文:
定理 iSup_eq_bot
  结论: iSup s = ⊥ ↔ 对任意 i, s i = ⊥
  证明: sSup_eq_bot.trans forall_mem_range

@[to_dual (attr := simp) iInf_lt_top]

Depends on / 依赖: forall_mem_range, sSup_eq_bot, sSup_eq_bot.trans
-/
theorem iSup_eq_bot : iSup s = ⊥ ↔ forall i, s i = ⊥ :=
  sSup_eq_bot.trans forall_mem_range

@[to_dual (attr := simp) iInf_lt_top]
/--
lemma `bot_lt_iSup` / 引理 `bot_lt_iSup`

English:
lemma bot_lt_iSup
  statement: ⊥ < ⨆ i, s i ↔ exists i, ⊥ < s i
  proof: by simp [bot_lt_iff_ne_bot]

@[to_dual]

中文:
引理 bot_lt_iSup
  结论: ⊥ < ⨆ i, s i ↔ 存在 i, ⊥ < s i
  证明: by simp [bot_lt_iff_ne_bot]

@[to_dual]

Depends on / 依赖: bot_lt_iff_ne_bot
-/
lemma bot_lt_iSup : ⊥ < ⨆ i, s i ↔ exists i, ⊥ < s i := by simp [bot_lt_iff_ne_bot]

@[to_dual]
/--
theorem `iSup₂_eq_bot` / 定理 `iSup₂_eq_bot`

English:
theorem iSup₂_eq_bot
  given: {f : forall i, κ i -> α}
  statement: ⨆ (i) (j), f i j = ⊥ ↔ forall i j, f i j = ⊥
  proof: by
  simp

@[to_dual (attr := simp)]

中文:
定理 iSup₂_eq_bot
  条件: {f : 对任意 i, κ i -> α}
  结论: ⨆ (i) (j), f i j = ⊥ ↔ 对任意 i j, f i j = ⊥
  证明: by
  simp

@[to_dual (attr := simp)]
-/
theorem iSup₂_eq_bot {f : forall i, κ i -> α} : ⨆ (i) (j), f i j = ⊥ ↔ forall i j, f i j = ⊥ := by
  simp

@[to_dual (attr := simp)]
/--
theorem `iSup_pos` / 定理 `iSup_pos`

English:
theorem iSup_pos
  given: {p : Prop} {f : p -> α} (hp : p)
  statement: ⨆ h : p, f h = f hp
  proof: le_antisymm (iSup_le fun _ => le_rfl) (le_iSup _ _)

@[to_dual (attr := simp)]

中文:
定理 iSup_pos
  条件: {p : 命题} {f : p -> α} (hp : p)
  结论: ⨆ h : p, f h = f hp
  证明: le_antisymm (iSup_le fun _ => le_rfl) (le_iSup _ _)

@[to_dual (attr := simp)]

Depends on / 依赖: iSup_le, le_antisymm, le_iSup, le_rfl
-/
theorem iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f hp :=
  le_antisymm (iSup_le fun _ => le_rfl) (le_iSup _ _)

@[to_dual (attr := simp)]
/--
theorem `iSup_neg` / 定理 `iSup_neg`

English:
theorem iSup_neg
  given: {p : Prop} {f : p -> α} (hp : ¬p)
  statement: ⨆ h : p, f h = ⊥
  proof: le_antisymm (iSup_le fun h => (hp h).elim) bot_le

中文:
定理 iSup_neg
  条件: {p : 命题} {f : p -> α} (hp : ¬p)
  结论: ⨆ h : p, f h = ⊥
  证明: le_antisymm (iSup_le fun h => (hp h).elim) bot_le

Depends on / 依赖: bot_le, iSup_le, le_antisymm
-/
theorem iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥ :=
  le_antisymm (iSup_le fun h => (hp h).elim) bot_le

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `ciSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
@[to_dual iInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `ciInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/]
/--
theorem `iSup_eq_of_forall_le_of_forall_lt_exists_gt` / 定理 `iSup_eq_of_forall_le_of_forall_lt_exists_gt`

English:
theorem iSup_eq_of_forall_le_of_forall_lt_exists_gt
  statement: {f : ι -> α} (h₁ : forall i, f i <= b)
  proof: sSup_eq_of_forall_le_of_forall_lt_exists_gt (forall_mem_range.mpr h₁) fun w hw =>
exists_range_iff.mpr h₂ w hw

@[to_dual]

中文:
定理 iSup_eq_of_forall_le_of_forall_lt_exists_gt
  结论: {f : ι -> α} (h₁ : 对任意 i, f i <= b)
  证明: sSup_eq_of_forall_le_of_forall_lt_exists_gt (forall_mem_range.mpr h₁) fun w hw =>
exists_range_iff.mpr h₂ w hw

@[to_dual]

Depends on / 依赖: exists_range_iff, exists_range_iff.mpr, forall_mem_range, forall_mem_range.mpr, sSup_eq_of_forall_le_of_forall_lt_exists_gt
-/
theorem iSup_eq_of_forall_le_of_forall_lt_exists_gt {f : ι -> α} (h₁ : forall i, f i <= b)
    (h₂ : forall w, w < b -> exists i, w < f i) : ⨆ i : ι, f i = b :=
  sSup_eq_of_forall_le_of_forall_lt_exists_gt (forall_mem_range.mpr h₁) fun w hw =>
exists_range_iff.mpr h₂ w hw

@[to_dual]
/--
theorem `iSup_eq_dif` / 定理 `iSup_eq_dif`

English:
theorem iSup_eq_dif
  given: {p : Prop} [Decidable p] (a : p -> α)
  proof: by by_cases h : p <;> simp [h]

@[to_dual]

中文:
定理 iSup_eq_dif
  条件: {p : 命题} [Decidable p] (a : p -> α)
  证明: by by_cases h : p <;> simp [h]

@[to_dual]
-/
theorem iSup_eq_dif {p : Prop} [Decidable p] (a : p -> α) :
    ⨆ h : p, a h = if h : p then a h else ⊥ := by by_cases h : p <;> simp [h]

@[to_dual]
/--
theorem `iSup_eq_if` / 定理 `iSup_eq_if`

English:
theorem iSup_eq_if
  given: {p : Prop} [Decidable p] (a : α)
  statement: ⨆ _ : p, a = if p then a else ⊥
  proof: iSup_eq_dif fun _ => a

@[to_dual]

中文:
定理 iSup_eq_if
  条件: {p : 命题} [Decidable p] (a : α)
  结论: ⨆ _ : p, a = if p then a else ⊥
  证明: iSup_eq_dif fun _ => a

@[to_dual]

Depends on / 依赖: iSup_eq_dif
-/
theorem iSup_eq_if {p : Prop} [Decidable p] (a : α) : ⨆ _ : p, a = if p then a else ⊥ :=
  iSup_eq_dif fun _ => a

@[to_dual]
/--
theorem `iSup_comm` / 定理 `iSup_comm`

English:
theorem iSup_comm
  given: {f : ι -> ι' -> α}
  statement: ⨆ (i) (j), f i j = ⨆ (j) (i), f i j
  proof: le_antisymm (iSup_le fun i => iSup_mono fun j => le_iSup (fun i => f i j) i)
    (iSup_le fun _ => iSup_mono fun _ => le_iSup _ _)

@[to_dual]

中文:
定理 iSup_comm
  条件: {f : ι -> ι' -> α}
  结论: ⨆ (i) (j), f i j = ⨆ (j) (i), f i j
  证明: le_antisymm (iSup_le fun i => iSup_mono fun j => le_iSup (fun i => f i j) i)
    (iSup_le fun _ => iSup_mono fun _ => le_iSup _ _)

@[to_dual]

Depends on / 依赖: iSup_le, iSup_mono, le_antisymm, le_iSup
-/
theorem iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), f i j :=
  le_antisymm (iSup_le fun i => iSup_mono fun j => le_iSup (fun i => f i j) i)
    (iSup_le fun _ => iSup_mono fun _ => le_iSup _ _)

@[to_dual]
/--
theorem `iSup₂_comm` / 定理 `iSup₂_comm`

English:
theorem iSup₂_comm
  statement: {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -> Sort*}
  proof: by
  simp only [@iSup_comm _ (κ₁ _), @iSup_comm _ ι₁]

@[to_dual (attr := simp)]

中文:
定理 iSup₂_comm
  结论: {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -> Sort*}
  证明: by
  simp only [@iSup_comm _ (κ₁ _), @iSup_comm _ ι₁]

@[to_dual (attr := simp)]

Depends on / 依赖: iSup_comm
-/
theorem iSup₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -> Sort*}
    (f : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> α) :
    ⨆ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂ = ⨆ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@iSup_comm _ (κ₁ _), @iSup_comm _ ι₁]

@[to_dual (attr := simp)]
/--
theorem `iSup_iSup_eq_left` / 定理 `iSup_iSup_eq_left`

English:
theorem iSup_iSup_eq_left
  given: {b : β} {f : forall x : β, x = b -> α}
  statement: ⨆ x, ⨆ h : x = b, f x h = f b rfl
  proof: le_antisymm (iSup₂_le fun _ h => h ▸ le_rfl) (le_iSup₂ (f := f) b rfl)

@[to_dual (attr := simp)]

中文:
定理 iSup_iSup_eq_left
  条件: {b : β} {f : 对任意 x : β, x = b -> α}
  结论: ⨆ x, ⨆ h : x = b, f x h = f b rfl
  证明: le_antisymm (iSup₂_le fun _ h => h ▸ le_rfl) (le_iSup₂ (f := f) b rfl)

@[to_dual (attr := simp)]

Depends on / 依赖: le_antisymm, le_rfl
-/
theorem iSup_iSup_eq_left {b : β} {f : forall x : β, x = b -> α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl :=
  le_antisymm (iSup₂_le fun _ h => h ▸ le_rfl) (le_iSup₂ (f := f) b rfl)

@[to_dual (attr := simp)]
/--
theorem `iSup_iSup_eq_right` / 定理 `iSup_iSup_eq_right`

English:
theorem iSup_iSup_eq_right
  given: {b : β} {f : forall x : β, b = x -> α}
  statement: ⨆ x, ⨆ h : b = x, f x h = f b rfl
  proof: le_antisymm (iSup₂_le fun _ h => h ▸ le_refl (f b rfl)) (le_iSup₂ b rfl)

@[to_dual]

中文:
定理 iSup_iSup_eq_right
  条件: {b : β} {f : 对任意 x : β, b = x -> α}
  结论: ⨆ x, ⨆ h : b = x, f x h = f b rfl
  证明: le_antisymm (iSup₂_le fun _ h => h ▸ le_refl (f b rfl)) (le_iSup₂ b rfl)

@[to_dual]

Depends on / 依赖: le_antisymm, le_refl
-/
theorem iSup_iSup_eq_right {b : β} {f : forall x : β, b = x -> α} : ⨆ x, ⨆ h : b = x, f x h = f b rfl :=
  le_antisymm (iSup₂_le fun _ h => h ▸ le_refl (f b rfl)) (le_iSup₂ b rfl)

@[to_dual]
/--
theorem `iSup_subtype` / 定理 `iSup_subtype`

English:
theorem iSup_subtype
  given: {p : ι -> Prop} {f : Subtype p -> α}
  statement: iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩
  proof: le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ p _ (fun i h => f ⟨i, h⟩) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]

中文:
定理 iSup_subtype
  条件: {p : ι -> 命题} {f : Subtype p -> α}
  结论: iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩
  证明: le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ p _ (fun i h => f ⟨i, h⟩) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]

Depends on / 依赖: iSup_le, le_antisymm, le_iSup
-/
theorem iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ p _ (fun i h => f ⟨i, h⟩) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]
/--
theorem `iSup_subtype'` / 定理 `iSup_subtype'`

English:
theorem iSup_subtype'
  given: {p : ι -> Prop} {f : forall i, p i -> α}
  proof: (@iSup_subtype _ _ _ p fun x => f x.val x.property).symm

@[to_dual]

中文:
定理 iSup_subtype'
  条件: {p : ι -> 命题} {f : 对任意 i, p i -> α}
  证明: (@iSup_subtype _ _ _ p fun x => f x.val x.property).symm

@[to_dual]

Depends on / 依赖: iSup_subtype, property, x.property, x.val
-/
theorem iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (@iSup_subtype _ _ _ p fun x => f x.val x.property).symm

@[to_dual]
/--
theorem `iSup_subtype''` / 定理 `iSup_subtype''`

English:
theorem iSup_subtype''
  given: {ι} (s : Set ι) (f : ι -> α)
  statement: ⨆ i : s, f i = ⨆ (t : ι) (_ : t in s), f t
  proof: iSup_subtype

@[to_dual]

中文:
定理 iSup_subtype''
  条件: {ι} (s : Set ι) (f : ι -> α)
  结论: ⨆ i : s, f i = ⨆ (t : ι) (_ : t in s), f t
  证明: iSup_subtype

@[to_dual]

Depends on / 依赖: iSup_subtype
-/
theorem iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f i = ⨆ (t : ι) (_ : t in s), f t :=
  iSup_subtype

@[to_dual]
/--
theorem `biSup_const` / 定理 `biSup_const`

English:
theorem biSup_const
  given: {a : α} {s : Set β} (hs : s.Nonempty)
  statement: ⨆ i in s, a = a
  proof: by
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  rw [← iSup_subtype'']; rw [iSup_const]

@[to_dual]

中文:
定理 biSup_const
  条件: {a : α} {s : Set β} (hs : s.Nonempty)
  结论: ⨆ i in s, a = a
  证明: by
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  rw [← iSup_subtype'']; rw [iSup_const]

@[to_dual]

Depends on / 依赖: Nonempty, Set.nonempty_coe_sort.mpr, iSup_const, iSup_subtype, nonempty_coe_sort
-/
theorem biSup_const {a : α} {s : Set β} (hs : s.Nonempty) : ⨆ i in s, a = a := by
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  rw [← iSup_subtype'']; rw [iSup_const]

@[to_dual]
/--
theorem `iSup_sup_eq` / 定理 `iSup_sup_eq`

English:
theorem iSup_sup_eq
  statement: ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
  proof: le_antisymm (iSup_le fun _ => sup_le_sup (le_iSup _ _) <| le_iSup _ _)
    (sup_le (iSup_mono fun _ => le_sup_left) <| iSup_mono fun _ => le_sup_right)

@[to_dual]

中文:
定理 iSup_sup_eq
  结论: ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x
  证明: le_antisymm (iSup_le fun _ => sup_le_sup (le_iSup _ _) <| le_iSup _ _)
    (sup_le (iSup_mono fun _ => le_sup_left) <| iSup_mono fun _ => le_sup_right)

@[to_dual]

Depends on / 依赖: iSup_le, iSup_mono, le_antisymm, le_iSup, le_sup_left, le_sup_right, sup_le, sup_le_sup
-/
theorem iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (iSup_le fun _ => sup_le_sup (le_iSup _ _) <| le_iSup _ _)
    (sup_le (iSup_mono fun _ => le_sup_left) <| iSup_mono fun _ => le_sup_right)

@[to_dual]
/--
lemma `Equiv.biSup_comp` / 引理 `Equiv.biSup_comp`

English:
lemma Equiv.biSup_comp
  given: {ι ι' : Type*} {g : ι' -> α} (e : ι ≃ ι') (s : Set ι')
  proof: by
  simpa only [iSup_subtype'] using! (image e.symm s).symm.iSup_comp (g := g ∘ (↑))

@[to_dual biInf_le]

中文:
引理 Equiv.biSup_comp
  条件: {ι ι' : 类型} {g : ι' -> α} (e : ι ≃ ι') (s : Set ι')
  证明: by
  simpa only [iSup_subtype'] using! (image e.symm s).symm.iSup_comp (g := g ∘ (↑))

@[to_dual biInf_le]

Depends on / 依赖: e.symm, iSup_comp, iSup_subtype, symm.iSup_comp
-/
lemma Equiv.biSup_comp {ι ι' : Type*} {g : ι' -> α} (e : ι ≃ ι') (s : Set ι') :
    ⨆ i in e.symm '' s, g (e i) = ⨆ i in s, g i := by
  simpa only [iSup_subtype'] using! (image e.symm s).symm.iSup_comp (g := g ∘ (↑))

@[to_dual biInf_le]
/--
lemma `le_biSup` / 引理 `le_biSup`

English:
lemma le_biSup
  given: {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i in s)
  statement: f i <= ⨆ i in s, f i
  proof: le_iSup₂_of_le i hi le_rfl

中文:
引理 le_biSup
  条件: {ι : 类型} {s : Set ι} (f : ι -> α) {i : ι} (hi : i in s)
  结论: f i <= ⨆ i in s, f i
  证明: le_iSup₂_of_le i hi le_rfl

Depends on / 依赖: le_rfl
-/
lemma le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i in s) : f i <= ⨆ i in s, f i :=
  le_iSup₂_of_le i hi le_rfl

/--
lemma `biInf_le_biSup` / 引理 `biInf_le_biSup`

English:
lemma biInf_le_biSup
  given: {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f : ι -> α}
  proof: (biInf_le _ hs.choose_spec).trans le_biSup _ hs.choose_spec

@[to_dual]

中文:
引理 biInf_le_biSup
  条件: {ι : 类型} {s : Set ι} (hs : s.Nonempty) {f : ι -> α}
  证明: (biInf_le _ hs.choose_spec).trans le_biSup _ hs.choose_spec

@[to_dual]

Depends on / 依赖: biInf_le, choose_spec, hs.choose_spec, le_biSup
-/
lemma biInf_le_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) {f : ι -> α} :
    ⨅ i in s, f i <= ⨆ i in s, f i :=
(biInf_le _ hs.choose_spec).trans le_biSup _ hs.choose_spec

@[to_dual]
/--
theorem `iSup_sup` / 定理 `iSup_sup`

English:
theorem iSup_sup
  given: [Nonempty ι] {f : ι -> α} {a : α}
  statement: (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a
  proof: by
  rw [iSup_sup_eq]; rw [iSup_const]

@[to_dual]

中文:
定理 iSup_sup
  条件: [Nonempty ι] {f : ι -> α} {a : α}
  结论: (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a
  证明: by
  rw [iSup_sup_eq]; rw [iSup_const]

@[to_dual]

Depends on / 依赖: iSup_const, iSup_sup_eq
-/
theorem iSup_sup [Nonempty ι] {f : ι -> α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a := by
  rw [iSup_sup_eq]; rw [iSup_const]

@[to_dual]
/--
theorem `sup_iSup` / 定理 `sup_iSup`

English:
theorem sup_iSup
  given: [Nonempty ι] {f : ι -> α} {a : α}
  statement: (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x
  proof: by
  rw [iSup_sup_eq]; rw [iSup_const]

@[to_dual]

中文:
定理 sup_iSup
  条件: [Nonempty ι] {f : ι -> α} {a : α}
  结论: (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x
  证明: by
  rw [iSup_sup_eq]; rw [iSup_const]

@[to_dual]

Depends on / 依赖: iSup_const, iSup_sup_eq
-/
theorem sup_iSup [Nonempty ι] {f : ι -> α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x := by
  rw [iSup_sup_eq]; rw [iSup_const]

@[to_dual]
/--
theorem `biSup_sup` / 定理 `biSup_sup`

English:
theorem biSup_sup
  given: {p : ι -> Prop} {f : forall i, p i -> α} {a : α} (h : exists i, p i)
  proof: by
  have : Nonempty { i // p i } :=
    let ⟨i, hi⟩ := h
    ⟨⟨i, hi⟩⟩
  rw [iSup_subtype']; rw [iSup_subtype']; rw [iSup_sup]

@[to_dual]

中文:
定理 biSup_sup
  条件: {p : ι -> 命题} {f : 对任意 i, p i -> α} {a : α} (h : 存在 i, p i)
  证明: by
  have : Nonempty { i // p i } :=
    let ⟨i, hi⟩ := h
    ⟨⟨i, hi⟩⟩
  rw [iSup_subtype']; rw [iSup_subtype']; rw [iSup_sup]

@[to_dual]

Depends on / 依赖: Nonempty, iSup_subtype, iSup_sup
-/
theorem biSup_sup {p : ι -> Prop} {f : forall i, p i -> α} {a : α} (h : exists i, p i) :
    (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a := by
  have : Nonempty { i // p i } :=
    let ⟨i, hi⟩ := h
    ⟨⟨i, hi⟩⟩
  rw [iSup_subtype']; rw [iSup_subtype']; rw [iSup_sup]

@[to_dual]
/--
theorem `sup_biSup` / 定理 `sup_biSup`

English:
theorem sup_biSup
  given: {p : ι -> Prop} {f : forall i, p i -> α} {a : α} (h : exists i, p i)
  proof: by
  simpa only [sup_comm] using @biSup_sup α _ _ p _ _ h

@[to_dual (dont_translate := ι)]

中文:
定理 sup_biSup
  条件: {p : ι -> 命题} {f : 对任意 i, p i -> α} {a : α} (h : 存在 i, p i)
  证明: by
  simpa only [sup_comm] using @biSup_sup α _ _ p _ _ h

@[to_dual (dont_translate := ι)]

Depends on / 依赖: biSup_sup, sup_comm
-/
theorem sup_biSup {p : ι -> Prop} {f : forall i, p i -> α} {a : α} (h : exists i, p i) :
    (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h := by
  simpa only [sup_comm] using @biSup_sup α _ _ p _ _ h

@[to_dual (dont_translate := ι)]
/--
lemma `biSup_lt_eq_iSup` / 引理 `biSup_lt_eq_iSup`

English:
lemma biSup_lt_eq_iSup
  given: {ι : Type*} [LT ι] [NoMaxOrder ι] {f : ι -> α}
  proof: by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · refine iSup_le fun j => ?_
    obtain ⟨i, jlt⟩ := exists_gt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]

中文:
引理 biSup_lt_eq_iSup
  条件: {ι : 类型} [LT ι] [NoMaxOrder ι] {f : ι -> α}
  证明: by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · refine iSup_le fun j => ?_
    obtain ⟨i, jlt⟩ := exists_gt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]

Depends on / 依赖: exists_gt, iSup_le, le_antisymm, le_iSup, le_iSup_of_le, le_rfl
-/
lemma biSup_lt_eq_iSup {ι : Type*} [LT ι] [NoMaxOrder ι] {f : ι -> α} :
    ⨆ (i) (j < i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · refine iSup_le fun j => ?_
    obtain ⟨i, jlt⟩ := exists_gt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]
/--
lemma `biSup_le_eq_iSup` / 引理 `biSup_le_eq_iSup`

English:
lemma biSup_le_eq_iSup
  given: {ι : Type*} [Preorder ι] {f : ι -> α}
  proof: by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · exact iSup_le fun j => le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual (dont_translate := ι)]

中文:
引理 biSup_le_eq_iSup
  条件: {ι : 类型} [Preorder ι] {f : ι -> α}
  证明: by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · exact iSup_le fun j => le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual (dont_translate := ι)]

Depends on / 依赖: iSup_le, le_antisymm, le_iSup, le_iSup_of_le, le_rfl
-/
lemma biSup_le_eq_iSup {ι : Type*} [Preorder ι] {f : ι -> α} :
    ⨆ (i) (j <= i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · exact iSup_le fun j => le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual (dont_translate := ι)]
/--
lemma `biSup_gt_eq_iSup` / 引理 `biSup_gt_eq_iSup`

English:
lemma biSup_gt_eq_iSup
  given: {ι : Type*} [LT ι] [NoMinOrder ι] {f : ι -> α}
  proof: by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · refine iSup_le fun j => ?_
    obtain ⟨i, jlt⟩ := exists_lt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]

中文:
引理 biSup_gt_eq_iSup
  条件: {ι : 类型} [LT ι] [NoMinOrder ι] {f : ι -> α}
  证明: by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · refine iSup_le fun j => ?_
    obtain ⟨i, jlt⟩ := exists_lt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]

Depends on / 依赖: exists_lt, iSup_le, le_antisymm, le_iSup, le_iSup_of_le, le_rfl
-/
lemma biSup_gt_eq_iSup {ι : Type*} [LT ι] [NoMinOrder ι] {f : ι -> α} :
    ⨆ (i) (j > i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · refine iSup_le fun j => ?_
    obtain ⟨i, jlt⟩ := exists_lt j
    exact le_iSup_of_le i (le_iSup₂_of_le j jlt le_rfl)

@[to_dual (dont_translate := ι)]
/--
lemma `biSup_ge_eq_iSup` / 引理 `biSup_ge_eq_iSup`

English:
lemma biSup_ge_eq_iSup
  given: {ι : Type*} [Preorder ι] {f : ι -> α}
  statement: ⨆ (i) (j >= i), f j = ⨆ i, f i
  proof: by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · exact iSup_le fun j => le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual biInf_ge_eq_of_monotone]

中文:
引理 biSup_ge_eq_iSup
  条件: {ι : 类型} [Preorder ι] {f : ι -> α}
  结论: ⨆ (i) (j >= i), f j = ⨆ i, f i
  证明: by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · exact iSup_le fun j => le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual biInf_ge_eq_of_monotone]

Depends on / 依赖: iSup_le, le_antisymm, le_iSup, le_iSup_of_le, le_rfl
-/
lemma biSup_ge_eq_iSup {ι : Type*} [Preorder ι] {f : ι -> α} : ⨆ (i) (j >= i), f j = ⨆ i, f i := by
  apply le_antisymm
  · exact iSup_le fun _ => iSup₂_le fun _ _ => le_iSup _ _
  · exact iSup_le fun j => le_iSup_of_le j (le_iSup₂_of_le j le_rfl le_rfl)

@[to_dual biInf_ge_eq_of_monotone]
/--
lemma `biSup_le_eq_of_monotone` / 引理 `biSup_le_eq_of_monotone`

English:
lemma biSup_le_eq_of_monotone
  given: [Preorder β] {f : β -> α} (hf : Monotone f) (b : β)
  proof: le_antisymm (iSup₂_le_iff.2 (fun _ hji => hf hji))
    (le_iSup_of_le b (ge_of_eq (iSup_pos le_rfl)))

@[to_dual biSup_ge_eq_of_antitone]

中文:
引理 biSup_le_eq_of_monotone
  条件: [Preorder β] {f : β -> α} (hf : Monotone f) (b : β)
  证明: le_antisymm (iSup₂_le_iff.2 (fun _ hji => hf hji))
    (le_iSup_of_le b (ge_of_eq (iSup_pos le_rfl)))

@[to_dual biSup_ge_eq_of_antitone]

Depends on / 依赖: ge_of_eq, iSup_pos, le_antisymm, le_iSup_of_le, le_rfl
-/
lemma biSup_le_eq_of_monotone [Preorder β] {f : β -> α} (hf : Monotone f) (b : β) :
    ⨆ (b' <= b), f b' = f b :=
  le_antisymm (iSup₂_le_iff.2 (fun _ hji => hf hji))
    (le_iSup_of_le b (ge_of_eq (iSup_pos le_rfl)))

@[to_dual biSup_ge_eq_of_antitone]
/--
lemma `biInf_le_eq_of_antitone` / 引理 `biInf_le_eq_of_antitone`

English:
lemma biInf_le_eq_of_antitone
  given: [Preorder β] {f : β -> α} (hf : Antitone f) (b : β)
  proof: le_antisymm (iInf₂_le_of_le b le_rfl le_rfl)
    (le_iInf₂ fun _ hji => hf hji)

中文:
引理 biInf_le_eq_of_antitone
  条件: [Preorder β] {f : β -> α} (hf : Antitone f) (b : β)
  证明: le_antisymm (iInf₂_le_of_le b le_rfl le_rfl)
    (le_iInf₂ fun _ hji => hf hji)

Depends on / 依赖: le_antisymm, le_rfl
-/
lemma biInf_le_eq_of_antitone [Preorder β] {f : β -> α} (hf : Antitone f) (b : β) :
    ⨅ (b' <= b), f b' = f b :=
  le_antisymm (iInf₂_le_of_le b le_rfl le_rfl)
    (le_iInf₂ fun _ hji => hf hji)

/-! ### `iSup` and `iInf` under `Prop` -/

@[to_dual]
/--
theorem `iSup_false` / 定理 `iSup_false`

English:
theorem iSup_false
  given: {s : False -> α}
  statement: iSup s = ⊥
  proof: by simp

@[to_dual]

中文:
定理 iSup_false
  条件: {s : False -> α}
  结论: iSup s = ⊥
  证明: by simp

@[to_dual]
-/
theorem iSup_false {s : False -> α} : iSup s = ⊥ := by simp

@[to_dual]
/--
theorem `iSup_true` / 定理 `iSup_true`

English:
theorem iSup_true
  given: {s : True -> α}
  statement: iSup s = s trivial
  proof: iSup_pos trivial

@[to_dual (attr := simp)]

中文:
定理 iSup_true
  条件: {s : True -> α}
  结论: iSup s = s trivial
  证明: iSup_pos trivial

@[to_dual (attr := simp)]

Depends on / 依赖: iSup_pos
-/
theorem iSup_true {s : True -> α} : iSup s = s trivial :=
  iSup_pos trivial

@[to_dual (attr := simp)]
/--
theorem `iSup_exists` / 定理 `iSup_exists`

English:
theorem iSup_exists
  given: {p : ι -> Prop} {f : Exists p -> α}
  statement: ⨆ x, f x = ⨆ (i) (h), f ⟨i, h⟩
  proof: le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]

中文:
定理 iSup_exists
  条件: {p : ι -> 命题} {f : Exists p -> α}
  结论: ⨆ x, f x = ⨆ (i) (h), f ⟨i, h⟩
  证明: le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]

Depends on / 依赖: iSup_le, le_antisymm, le_iSup
-/
theorem iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x = ⨆ (i) (h), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

@[to_dual]
/--
theorem `iSup_and` / 定理 `iSup_and`

English:
theorem iSup_and
  given: {p q : Prop} {s : p ∧ q -> α}
  statement: iSup s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩
  proof: le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

中文:
定理 iSup_and
  条件: {p q : 命题} {s : p ∧ q -> α}
  结论: iSup s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩
  证明: le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

Depends on / 依赖: iSup_le, le_antisymm, le_iSup
-/
theorem iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)

/-- The symmetric case of `iSup_and`, useful for rewriting into a supremum over a conjunction -/
@[to_dual /-- The symmetric case of `iInf_and`,
useful for rewriting into an infimum over a conjunction. -/]
/--
theorem `iSup_and'` / 定理 `iSup_and'`

English:
theorem iSup_and'
  given: {p q : Prop} {s : p -> q -> α}
  proof: Eq.symm iSup_and

@[to_dual]

中文:
定理 iSup_and'
  条件: {p q : 命题} {s : p -> q -> α}
  证明: Eq.symm iSup_and

@[to_dual]

Depends on / 依赖: Eq.symm, iSup_and
-/
theorem iSup_and' {p q : Prop} {s : p -> q -> α} :
    ⨆ (h₁ : p) (h₂ : q), s h₁ h₂ = ⨆ h : p ∧ q, s h.1 h.2 :=
  Eq.symm iSup_and

@[to_dual]
/--
theorem `iSup_or` / 定理 `iSup_or`

English:
theorem iSup_or
  given: {p q : Prop} {s : p ∨ q -> α}
  proof: le_antisymm
    (iSup_le fun i =>
      match i with
| Or.inl _ => le_sup_of_le_left le_iSup (fun _ => s _) _
| Or.inr _ => le_sup_of_le_right le_iSup (fun _ => s _) _)
    (sup_le (iSup_comp_le _ _) (iSup_comp_le _ _))

中文:
定理 iSup_or
  条件: {p q : 命题} {s : p ∨ q -> α}
  证明: le_antisymm
    (iSup_le fun i =>
      match i with
| Or.inl _ => le_sup_of_le_left le_iSup (fun _ => s _) _
| Or.inr _ => le_sup_of_le_right le_iSup (fun _ => s _) _)
    (sup_le (iSup_comp_le _ _) (iSup_comp_le _ _))

Depends on / 依赖: Or.inl, Or.inr, iSup_comp_le, iSup_le, le_antisymm, le_iSup, le_sup_of_le_left, le_sup_of_le_right, sup_le
-/
theorem iSup_or {p q : Prop} {s : p ∨ q -> α} :
    ⨆ x, s x = (⨆ i, s (Or.inl i)) ⊔ ⨆ j, s (Or.inr j) :=
  le_antisymm
    (iSup_le fun i =>
      match i with
| Or.inl _ => le_sup_of_le_left le_iSup (fun _ => s _) _
| Or.inr _ => le_sup_of_le_right le_iSup (fun _ => s _) _)
    (sup_le (iSup_comp_le _ _) (iSup_comp_le _ _))

section

variable (p : ι -> Prop) [DecidablePred p]

@[to_dual]
/--
theorem `iSup_dite` / 定理 `iSup_dite`

English:
theorem iSup_dite
  given: (f : forall i, p i -> α) (g : forall i, ¬p i -> α)
  proof: by
  rw [← iSup_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]

@[to_dual]

中文:
定理 iSup_dite
  条件: (f : 对任意 i, p i -> α) (g : 对任意 i, ¬p i -> α)
  证明: by
  rw [← iSup_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]

@[to_dual]

Depends on / 依赖: iSup_sup_eq, split_ifs
-/
theorem iSup_dite (f : forall i, p i -> α) (g : forall i, ¬p i -> α) :
    ⨆ i, (if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i),
    g i h := by
  rw [← iSup_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]

@[to_dual]
/--
theorem `iSup_ite` / 定理 `iSup_ite`

English:
theorem iSup_ite
  given: (f g : ι -> α)
  proof: iSup_dite _ _ _

中文:
定理 iSup_ite
  条件: (f g : ι -> α)
  证明: iSup_dite _ _ _

Depends on / 依赖: iSup_dite
-/
theorem iSup_ite (f g : ι -> α) :
    ⨆ i, (if p i then f i else g i) = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), g i :=
  iSup_dite _ _ _

end

@[to_dual]
/--
theorem `iSup_range` / 定理 `iSup_range`

English:
theorem iSup_range
  given: {g : β -> α} {f : ι -> β}
  statement: ⨆ b in range f, g b = ⨆ i, g (f i)
  proof: by
  rw [← iSup_subtype'']; rw [iSup_range']

@[to_dual]

中文:
定理 iSup_range
  条件: {g : β -> α} {f : ι -> β}
  结论: ⨆ b in range f, g b = ⨆ i, g (f i)
  证明: by
  rw [← iSup_subtype'']; rw [iSup_range']

@[to_dual]

Depends on / 依赖: iSup_range, iSup_subtype
-/
theorem iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b = ⨆ i, g (f i) := by
  rw [← iSup_subtype'']; rw [iSup_range']

@[to_dual]
/--
theorem `sSup_image` / 定理 `sSup_image`

English:
theorem sSup_image
  given: {s : Set β} {f : β -> α}
  statement: sSup (f '' s) = ⨆ a in s, f a
  proof: by
  rw [← iSup_subtype'']; rw [sSup_image']

@[to_dual]

中文:
定理 sSup_image
  条件: {s : Set β} {f : β -> α}
  结论: sSup (f '' s) = ⨆ a in s, f a
  证明: by
  rw [← iSup_subtype'']; rw [sSup_image']

@[to_dual]

Depends on / 依赖: iSup_subtype, sSup_image
-/
theorem sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in s, f a := by
  rw [← iSup_subtype'']; rw [sSup_image']

@[to_dual]
/--
theorem `OrderIso.map_sSup_eq_sSup_symm_preimage` / 定理 `OrderIso.map_sSup_eq_sSup_symm_preimage`

English:
theorem OrderIso.map_sSup_eq_sSup_symm_preimage
  given: [CompleteLattice β] (f : α ≃o β) (s : Set α)
  proof: by
  rw [map_sSup]; rw [← sSup_image]; rw [f.image_eq_preimage_symm]

中文:
定理 OrderIso.map_sSup_eq_sSup_symm_preimage
  条件: [CompleteLattice β] (f : α ≃o β) (s : Set α)
  证明: by
  rw [map_sSup]; rw [← sSup_image]; rw [f.image_eq_preimage_symm]

Depends on / 依赖: f.image_eq_preimage_symm, image_eq_preimage_symm, map_sSup, sSup_image
-/
theorem OrderIso.map_sSup_eq_sSup_symm_preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = sSup (f.symm ⁻¹' s) := by
  rw [map_sSup]; rw [← sSup_image]; rw [f.image_eq_preimage_symm]

/-
### iSup and iInf under set constructions
-/

@[to_dual]
/--
theorem `iSup_emptyset` / 定理 `iSup_emptyset`

English:
theorem iSup_emptyset
  given: {f : β -> α}
  statement: ⨆ x in (∅ : Set β), f x = ⊥
  proof: by simp

@[to_dual]

中文:
定理 iSup_emptyset
  条件: {f : β -> α}
  结论: ⨆ x in (∅ : Set β), f x = ⊥
  证明: by simp

@[to_dual]
-/
theorem iSup_emptyset {f : β -> α} : ⨆ x in (∅ : Set β), f x = ⊥ := by simp

@[to_dual]
/--
theorem `iSup_univ` / 定理 `iSup_univ`

English:
theorem iSup_univ
  given: {f : β -> α}
  statement: ⨆ x in (univ : Set β), f x = ⨆ x, f x
  proof: by simp

@[to_dual]

中文:
定理 iSup_univ
  条件: {f : β -> α}
  结论: ⨆ x in (univ : Set β), f x = ⨆ x, f x
  证明: by simp

@[to_dual]
-/
theorem iSup_univ {f : β -> α} : ⨆ x in (univ : Set β), f x = ⨆ x, f x := by simp

@[to_dual]
/--
theorem `iSup_union` / 定理 `iSup_union`

English:
theorem iSup_union
  given: {f : β -> α} {s t : Set β}
  proof: by
  simp_rw [mem_union, iSup_or, iSup_sup_eq]

@[to_dual]

中文:
定理 iSup_union
  条件: {f : β -> α} {s t : Set β}
  证明: by
  simp_rw [mem_union, iSup_or, iSup_sup_eq]

@[to_dual]

Depends on / 依赖: iSup_or, iSup_sup_eq, mem_union, simp_rw
-/
theorem iSup_union {f : β -> α} {s t : Set β} :
    ⨆ x in s union t, f x = (⨆ x in s, f x) ⊔ ⨆ x in t, f x := by
  simp_rw [mem_union, iSup_or, iSup_sup_eq]

@[to_dual]
/--
theorem `iSup_split` / 定理 `iSup_split`

English:
theorem iSup_split
  given: (f : β -> α) (p : β -> Prop)
  proof: by
  simpa [Classical.em] using @iSup_union _ _ _ f { i | p i } { i | ¬p i }

@[to_dual]

中文:
定理 iSup_split
  条件: (f : β -> α) (p : β -> 命题)
  证明: by
  simpa [Classical.em] using @iSup_union _ _ _ f { i | p i } { i | ¬p i }

@[to_dual]

Depends on / 依赖: Classical, Classical.em, iSup_union
-/
theorem iSup_split (f : β -> α) (p : β -> Prop) :
    ⨆ i, f i = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i := by
  simpa [Classical.em] using @iSup_union _ _ _ f { i | p i } { i | ¬p i }

@[to_dual]
/--
theorem `iSup_split_single` / 定理 `iSup_split_single`

English:
theorem iSup_split_single
  given: (f : β -> α) (i₀ : β)
  statement: ⨆ i, f i = f i₀ ⊔ ⨆ (i) (_ : i != i₀), f i
  proof: by
  convert! iSup_split f (fun i => i = i₀)
  simp

@[to_dual]

中文:
定理 iSup_split_single
  条件: (f : β -> α) (i₀ : β)
  结论: ⨆ i, f i = f i₀ ⊔ ⨆ (i) (_ : i != i₀), f i
  证明: by
  convert! iSup_split f (fun i => i = i₀)
  simp

@[to_dual]

Depends on / 依赖: convert, iSup_split
-/
theorem iSup_split_single (f : β -> α) (i₀ : β) : ⨆ i, f i = f i₀ ⊔ ⨆ (i) (_ : i != i₀), f i := by
  convert! iSup_split f (fun i => i = i₀)
  simp

@[to_dual]
/--
theorem `iSup_le_iSup_of_subset` / 定理 `iSup_le_iSup_of_subset`

English:
theorem iSup_le_iSup_of_subset
  given: {f : β -> α} {s t : Set β}
  statement: s subseteq t -> ⨆ x in s, f x <= ⨆ x in t, f x
  proof: biSup_mono

@[to_dual]

中文:
定理 iSup_le_iSup_of_subset
  条件: {f : β -> α} {s t : Set β}
  结论: s subseteq t -> ⨆ x in s, f x <= ⨆ x in t, f x
  证明: biSup_mono

@[to_dual]

Depends on / 依赖: biSup_mono
-/
theorem iSup_le_iSup_of_subset {f : β -> α} {s t : Set β} : s subseteq t -> ⨆ x in s, f x <= ⨆ x in t, f x :=
  biSup_mono

@[to_dual]
/--
theorem `iSup_insert` / 定理 `iSup_insert`

English:
theorem iSup_insert
  given: {f : β -> α} {s : Set β} {b : β}
  proof: by
  simp [iSup_or, iSup_sup_eq]

@[to_dual]

中文:
定理 iSup_insert
  条件: {f : β -> α} {s : Set β} {b : β}
  证明: by
  simp [iSup_or, iSup_sup_eq]

@[to_dual]

Depends on / 依赖: iSup_or, iSup_sup_eq
-/
theorem iSup_insert {f : β -> α} {s : Set β} {b : β} :
    ⨆ x in insert b s, f x = f b ⊔ ⨆ x in s, f x := by
  simp [iSup_or, iSup_sup_eq]

@[to_dual]
/--
theorem `iSup_singleton` / 定理 `iSup_singleton`

English:
theorem iSup_singleton
  given: {f : β -> α} {b : β}
  statement: ⨆ x in (singleton b : Set β), f x = f b
  proof: by simp

@[to_dual]

中文:
定理 iSup_singleton
  条件: {f : β -> α} {b : β}
  结论: ⨆ x in (singleton b : Set β), f x = f b
  证明: by simp

@[to_dual]
-/
theorem iSup_singleton {f : β -> α} {b : β} : ⨆ x in (singleton b : Set β), f x = f b := by simp

@[to_dual]
/--
theorem `iSup_pair` / 定理 `iSup_pair`

English:
theorem iSup_pair
  given: {f : β -> α} {a b : β}
  statement: ⨆ x in ({a, b} : Set β), f x = f a ⊔ f b
  proof: by
  rw [iSup_insert]; rw [iSup_singleton]

@[to_dual]

中文:
定理 iSup_pair
  条件: {f : β -> α} {a b : β}
  结论: ⨆ x in ({a, b} : Set β), f x = f a ⊔ f b
  证明: by
  rw [iSup_insert]; rw [iSup_singleton]

@[to_dual]

Depends on / 依赖: iSup_insert, iSup_singleton
-/
theorem iSup_pair {f : β -> α} {a b : β} : ⨆ x in ({a, b} : Set β), f x = f a ⊔ f b := by
  rw [iSup_insert]; rw [iSup_singleton]

@[to_dual]
/--
theorem `iSup_image` / 定理 `iSup_image`

English:
theorem iSup_image
  given: {γ} {f : β -> γ} {g : γ -> α} {t : Set β}
  proof: by
  rw [← sSup_image]; rw [← sSup_image]; rw [← image_comp]; rw [comp_def]

@[to_dual]

中文:
定理 iSup_image
  条件: {γ} {f : β -> γ} {g : γ -> α} {t : Set β}
  证明: by
  rw [← sSup_image]; rw [← sSup_image]; rw [← image_comp]; rw [comp_def]

@[to_dual]

Depends on / 依赖: comp_def, image_comp, sSup_image
-/
theorem iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} :
    ⨆ c in f '' t, g c = ⨆ b in t, g (f b) := by
  rw [← sSup_image]; rw [← sSup_image]; rw [← image_comp]; rw [comp_def]

@[to_dual]
/--
theorem `iSup_extend_bot` / 定理 `iSup_extend_bot`

English:
theorem iSup_extend_bot
  given: {e : ι -> β} (he : Injective e) (f : ι -> α)
  proof: by
  rw [iSup_split _ fun j => exists i]; rw [e i = j]
  simp +contextual [he.extend_apply, extend_apply', @iSup_comm _ β ι]

@[to_dual]

中文:
定理 iSup_extend_bot
  条件: {e : ι -> β} (he : Injective e) (f : ι -> α)
  证明: by
  rw [iSup_split _ fun j => exists i]; rw [e i = j]
  simp +contextual [he.extend_apply, extend_apply', @iSup_comm _ β ι]

@[to_dual]

Depends on / 依赖: contextual, extend_apply, he.extend_apply, iSup_comm, iSup_split
-/
theorem iSup_extend_bot {e : ι -> β} (he : Injective e) (f : ι -> α) :
    ⨆ j, extend e f ⊥ j = ⨆ i, f i := by
  rw [iSup_split _ fun j => exists i]; rw [e i = j]
  simp +contextual [he.extend_apply, extend_apply', @iSup_comm _ β ι]

@[to_dual]
/--
theorem `Set.BijOn.iSup_comp` / 定理 `Set.BijOn.iSup_comp`

English:
theorem Set.BijOn.iSup_comp
  statement: {s : Set β} {t : Set γ} {f : β -> γ} (g : γ -> α)
  proof: by
  rw [← hf.image_eq]; rw [iSup_image]

@[to_dual]

中文:
定理 Set.BijOn.iSup_comp
  结论: {s : Set β} {t : Set γ} {f : β -> γ} (g : γ -> α)
  证明: by
  rw [← hf.image_eq]; rw [iSup_image]

@[to_dual]

Depends on / 依赖: hf.image_eq, iSup_image, image_eq
-/
theorem Set.BijOn.iSup_comp {s : Set β} {t : Set γ} {f : β -> γ} (g : γ -> α)
    (hf : Set.BijOn f s t) : ⨆ x in s, g (f x) = ⨆ y in t, g y := by
  rw [← hf.image_eq]; rw [iSup_image]

@[to_dual]
/--
theorem `Set.BijOn.iSup_congr` / 定理 `Set.BijOn.iSup_congr`

English:
theorem Set.BijOn.iSup_congr
  statement: {s : Set β} {t : Set γ} (f : β -> α) (g : γ -> α) {h : β -> γ}
  proof: by
  simpa only [h2] using h1.iSup_comp g

中文:
定理 Set.BijOn.iSup_congr
  结论: {s : Set β} {t : Set γ} (f : β -> α) (g : γ -> α) {h : β -> γ}
  证明: by
  simpa only [h2] using h1.iSup_comp g

Depends on / 依赖: h1.iSup_comp, iSup_comp
-/
theorem Set.BijOn.iSup_congr {s : Set β} {t : Set γ} (f : β -> α) (g : γ -> α) {h : β -> γ}
    (h1 : Set.BijOn h s t) (h2 : forall x, g (h x) = f x) : ⨆ x in s, f x = ⨆ y in t, g y := by
  simpa only [h2] using h1.iSup_comp g

section le

variable {ι : Type*} [PartialOrder ι] (f : ι -> α) (i : ι)

@[to_dual (dont_translate := ι)]
/--
theorem `biSup_le_eq_sup` / 定理 `biSup_le_eq_sup`

English:
theorem biSup_le_eq_sup
  statement: (⨆ j <= i, f j) = (⨆ j < i, f j) ⊔ f i
  proof: by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [le_refl, iSup_pos, iSup_and', lt_iff_le_and_ne, and_comm, sup_comm]

@[to_dual (dont_translate := ι)]

中文:
定理 biSup_le_eq_sup
  结论: (⨆ j <= i, f j) = (⨆ j < i, f j) ⊔ f i
  证明: by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [le_refl, iSup_pos, iSup_and', lt_iff_le_and_ne, and_comm, sup_comm]

@[to_dual (dont_translate := ι)]

Depends on / 依赖: iSup_split_single
-/
theorem biSup_le_eq_sup : (⨆ j <= i, f j) = (⨆ j < i, f j) ⊔ f i := by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [le_refl, iSup_pos, iSup_and', lt_iff_le_and_ne, and_comm, sup_comm]

@[to_dual (dont_translate := ι)]
/--
theorem `biSup_ge_eq_sup` / 定理 `biSup_ge_eq_sup`

English:
theorem biSup_ge_eq_sup
  statement: (⨆ j >= i, f j) = f i ⊔ (⨆ j > i, f j)
  proof: by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [ge_iff_le, le_refl, iSup_pos, ne_comm, iSup_and', gt_iff_lt, lt_iff_le_and_ne,
    and_comm]

中文:
定理 biSup_ge_eq_sup
  结论: (⨆ j >= i, f j) = f i ⊔ (⨆ j > i, f j)
  证明: by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [ge_iff_le, le_refl, iSup_pos, ne_comm, iSup_and', gt_iff_lt, lt_iff_le_and_ne,
    and_comm]

Depends on / 依赖: iSup_split_single
-/
theorem biSup_ge_eq_sup : (⨆ j >= i, f j) = f i ⊔ (⨆ j > i, f j) := by
  rw [iSup_split_single _ i]
  -- Squeezed for a ~10x speedup, though it's still reasonably fast unsqueezed.
  simp only [ge_iff_le, le_refl, iSup_pos, ne_comm, iSup_and', gt_iff_lt, lt_iff_le_and_ne,
    and_comm]

end le

/-!
### `iSup` and `iInf` under `Type`
-/

@[to_dual iInf_of_isEmpty]
/--
theorem `iSup_of_empty'` / 定理 `iSup_of_empty'`

English:
theorem iSup_of_empty'
  given: {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
  statement: iSup f = sSup (∅ : Set α)
  proof: congr_arg sSup (range_eq_empty f)

@[to_dual]

中文:
定理 iSup_of_empty'
  条件: {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
  结论: iSup f = sSup (∅ : Set α)
  证明: congr_arg sSup (range_eq_empty f)

@[to_dual]

Depends on / 依赖: congr_arg, range_eq_empty
-/
theorem iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α) : iSup f = sSup (∅ : Set α) :=
  congr_arg sSup (range_eq_empty f)

@[to_dual]
/--
theorem `iSup_of_empty` / 定理 `iSup_of_empty`

English:
theorem iSup_of_empty
  given: [IsEmpty ι] (f : ι -> α)
  statement: iSup f = ⊥
  proof: (iSup_of_empty' f).trans sSup_empty

@[to_dual]

中文:
定理 iSup_of_empty
  条件: [IsEmpty ι] (f : ι -> α)
  结论: iSup f = ⊥
  证明: (iSup_of_empty' f).trans sSup_empty

@[to_dual]

Depends on / 依赖: iSup_of_empty, sSup_empty
-/
theorem iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥ :=
  (iSup_of_empty' f).trans sSup_empty

@[to_dual]
/--
theorem `isLUB_biSup` / 定理 `isLUB_biSup`

English:
theorem isLUB_biSup
  given: {s : Set β} {f : β -> α}
  statement: IsLUB (f '' s) (⨆ x in s, f x)
  proof: by
  simpa only [range_comp, Subtype.range_coe, iSup_subtype'] using!
    @isLUB_iSup α s _ (f ∘ fun x => (x : β))

@[to_dual]

中文:
定理 isLUB_biSup
  条件: {s : Set β} {f : β -> α}
  结论: IsLUB (f '' s) (⨆ x in s, f x)
  证明: by
  simpa only [range_comp, Subtype.range_coe, iSup_subtype'] using!
    @isLUB_iSup α s _ (f ∘ fun x => (x : β))

@[to_dual]

Depends on / 依赖: Subtype, Subtype.range_coe, iSup_subtype, isLUB_iSup, range_coe, range_comp
-/
theorem isLUB_biSup {s : Set β} {f : β -> α} : IsLUB (f '' s) (⨆ x in s, f x) := by
  simpa only [range_comp, Subtype.range_coe, iSup_subtype'] using!
    @isLUB_iSup α s _ (f ∘ fun x => (x : β))

@[to_dual]
/--
theorem `iSup_sigma` / 定理 `iSup_sigma`

English:
theorem iSup_sigma
  given: {p : β -> Type*} {f : Sigma p -> α}
  statement: ⨆ x, f x = ⨆ (i) (j), f ⟨i, j⟩
  proof: eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Sigma.forall]

@[to_dual]

中文:
定理 iSup_sigma
  条件: {p : β -> 类型} {f : Sigma p -> α}
  结论: ⨆ x, f x = ⨆ (i) (j), f ⟨i, j⟩
  证明: eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Sigma.forall]

@[to_dual]

Depends on / 依赖: Sigma.forall, eq_of_forall_ge_iff, iSup_le_iff
-/
theorem iSup_sigma {p : β -> Type*} {f : Sigma p -> α} : ⨆ x, f x = ⨆ (i) (j), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Sigma.forall]

@[to_dual]
/--
lemma `iSup_sigma'` / 引理 `iSup_sigma'`

English:
lemma iSup_sigma'
  given: {κ : β -> Type*} (f : forall i, κ i -> α)
  proof: (iSup_sigma (f := fun x => f x.1 x.2)).symm

@[to_dual]

中文:
引理 iSup_sigma'
  条件: {κ : β -> 类型} (f : 对任意 i, κ i -> α)
  证明: (iSup_sigma (f := fun x => f x.1 x.2)).symm

@[to_dual]

Depends on / 依赖: iSup_sigma
-/
lemma iSup_sigma' {κ : β -> Type*} (f : forall i, κ i -> α) :
    (⨆ i, ⨆ j, f i j) = ⨆ x : Σ i, κ i, f x.1 x.2 := (iSup_sigma (f := fun x => f x.1 x.2)).symm

@[to_dual]
/--
lemma `iSup_psigma` / 引理 `iSup_psigma`

English:
lemma iSup_psigma
  given: {ι : Sort*} {κ : ι -> Sort*} (f : (Σ' i, κ i) -> α)
  proof: eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, PSigma.forall]

@[to_dual]

中文:
引理 iSup_psigma
  条件: {ι : Sort*} {κ : ι -> Sort*} (f : (Σ' i, κ i) -> α)
  证明: eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, PSigma.forall]

@[to_dual]

Depends on / 依赖: PSigma, PSigma.forall, eq_of_forall_ge_iff, iSup_le_iff
-/
lemma iSup_psigma {ι : Sort*} {κ : ι -> Sort*} (f : (Σ' i, κ i) -> α) :
    ⨆ ij, f ij = ⨆ i, ⨆ j, f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, PSigma.forall]

@[to_dual]
/--
lemma `iSup_psigma'` / 引理 `iSup_psigma'`

English:
lemma iSup_psigma'
  given: {ι : Sort*} {κ : ι -> Sort*} (f : forall i, κ i -> α)
  proof: (iSup_psigma fun x => f x.1 x.2).symm

@[to_dual]

中文:
引理 iSup_psigma'
  条件: {ι : Sort*} {κ : ι -> Sort*} (f : 对任意 i, κ i -> α)
  证明: (iSup_psigma fun x => f x.1 x.2).symm

@[to_dual]

Depends on / 依赖: iSup_psigma
-/
lemma iSup_psigma' {ι : Sort*} {κ : ι -> Sort*} (f : forall i, κ i -> α) :
    (⨆ i, ⨆ j, f i j) = ⨆ ij : Σ' i, κ i, f ij.1 ij.2 := (iSup_psigma fun x => f x.1 x.2).symm

@[to_dual]
/--
theorem `iSup_prod` / 定理 `iSup_prod`

English:
theorem iSup_prod
  given: {f : β × γ -> α}
  statement: ⨆ x, f x = ⨆ (i) (j), f (i, j)
  proof: eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Prod.forall]

@[to_dual]

中文:
定理 iSup_prod
  条件: {f : β × γ -> α}
  结论: ⨆ x, f x = ⨆ (i) (j), f (i, j)
  证明: eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Prod.forall]

@[to_dual]

Depends on / 依赖: Prod.forall, eq_of_forall_ge_iff, iSup_le_iff
-/
theorem iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Prod.forall]

@[to_dual]
/--
lemma `iSup_prod'` / 引理 `iSup_prod'`

English:
lemma iSup_prod'
  given: (f : β -> γ -> α)
  statement: (⨆ i, ⨆ j, f i j) = ⨆ x : β × γ, f x.1 x.2
  proof: (iSup_prod (f := fun x => f x.1 x.2)).symm

@[to_dual]

中文:
引理 iSup_prod'
  条件: (f : β -> γ -> α)
  结论: (⨆ i, ⨆ j, f i j) = ⨆ x : β × γ, f x.1 x.2
  证明: (iSup_prod (f := fun x => f x.1 x.2)).symm

@[to_dual]

Depends on / 依赖: iSup_prod
-/
lemma iSup_prod' (f : β -> γ -> α) : (⨆ i, ⨆ j, f i j) = ⨆ x : β × γ, f x.1 x.2 :=
(iSup_prod (f := fun x => f x.1 x.2)).symm

@[to_dual]
/--
theorem `biSup_prod` / 定理 `biSup_prod`

English:
theorem biSup_prod
  given: {f : β × γ -> α} {s : Set β} {t : Set γ}
  proof: by
  simp_rw [iSup_prod, mem_prod, iSup_and]
  exact iSup_congr fun _ => iSup_comm

@[to_dual]

中文:
定理 biSup_prod
  条件: {f : β × γ -> α} {s : Set β} {t : Set γ}
  证明: by
  simp_rw [iSup_prod, mem_prod, iSup_and]
  exact iSup_congr fun _ => iSup_comm

@[to_dual]

Depends on / 依赖: iSup_and, iSup_comm, iSup_congr, iSup_prod, mem_prod, simp_rw
-/
theorem biSup_prod {f : β × γ -> α} {s : Set β} {t : Set γ} :
    ⨆ x in s ×ˢ t, f x = ⨆ (a in s) (b in t), f (a, b) := by
  simp_rw [iSup_prod, mem_prod, iSup_and]
  exact iSup_congr fun _ => iSup_comm

@[to_dual]
/--
theorem `biSup_prod'` / 定理 `biSup_prod'`

English:
theorem biSup_prod'
  given: {f : β -> γ -> α} {s : Set β} {t : Set γ}
  proof: biSup_prod

@[to_dual]

中文:
定理 biSup_prod'
  条件: {f : β -> γ -> α} {s : Set β} {t : Set γ}
  证明: biSup_prod

@[to_dual]

Depends on / 依赖: biSup_prod
-/
theorem biSup_prod' {f : β -> γ -> α} {s : Set β} {t : Set γ} :
    ⨆ x in s ×ˢ t, f x.1 x.2 = ⨆ (a in s) (b in t), f a b :=
  biSup_prod

@[to_dual]
/--
theorem `iSup_image2` / 定理 `iSup_image2`

English:
theorem iSup_image2
  given: {γ δ} (f : β -> γ -> δ) (s : Set β) (t : Set γ) (g : δ -> α)
  proof: by
  rw [← image_prod]; rw [iSup_image]; rw [biSup_prod]

@[to_dual]

中文:
定理 iSup_image2
  条件: {γ δ} (f : β -> γ -> δ) (s : Set β) (t : Set γ) (g : δ -> α)
  证明: by
  rw [← image_prod]; rw [iSup_image]; rw [biSup_prod]

@[to_dual]

Depends on / 依赖: biSup_prod, iSup_image, image_prod
-/
theorem iSup_image2 {γ δ} (f : β -> γ -> δ) (s : Set β) (t : Set γ) (g : δ -> α) :
    ⨆ d in image2 f s t, g d = ⨆ b in s, ⨆ c in t, g (f b c) := by
  rw [← image_prod]; rw [iSup_image]; rw [biSup_prod]

@[to_dual]
/--
theorem `iSup_sum` / 定理 `iSup_sum`

English:
theorem iSup_sum
  given: {f : β oplus γ -> α}
  statement: ⨆ x, f x = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j)
  proof: eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, iSup_le_iff, Sum.forall]

@[to_dual]

中文:
定理 iSup_sum
  条件: {f : β oplus γ -> α}
  结论: ⨆ x, f x = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j)
  证明: eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, iSup_le_iff, Sum.forall]

@[to_dual]

Depends on / 依赖: Sum.forall, eq_of_forall_ge_iff, iSup_le_iff, sup_le_iff
-/
theorem iSup_sum {f : β oplus γ -> α} : ⨆ x, f x = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j) :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, iSup_le_iff, Sum.forall]

@[to_dual]
/--
theorem `iSup_option` / 定理 `iSup_option`

English:
theorem iSup_option
  given: (f : Option β -> α)
  statement: ⨆ o, f o = f none ⊔ ⨆ b, f (Option.some b)
  proof: eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, sup_le_iff, Option.forall]

中文:
定理 iSup_option
  条件: (f : Option β -> α)
  结论: ⨆ o, f o = f none ⊔ ⨆ b, f (Option.some b)
  证明: eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, sup_le_iff, Option.forall]

Depends on / 依赖: Option.forall, eq_of_forall_ge_iff, iSup_le_iff, sup_le_iff
-/
theorem iSup_option (f : Option β -> α) : ⨆ o, f o = f none ⊔ ⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, sup_le_iff, Option.forall]

/-- A version of `iSup_option` useful for rewriting right-to-left. -/
@[to_dual /-- A version of `iInf_option` useful for rewriting right-to-left. -/]
/--
theorem `iSup_option_elim` / 定理 `iSup_option_elim`

English:
theorem iSup_option_elim
  given: (a : α) (f : β -> α)
  statement: ⨆ o : Option β, o.elim a f = a ⊔ ⨆ b, f b
  proof: by
  simp [iSup_option]

中文:
定理 iSup_option_elim
  条件: (a : α) (f : β -> α)
  结论: ⨆ o : Option β, o.elim a f = a ⊔ ⨆ b, f b
  证明: by
  simp [iSup_option]

Depends on / 依赖: iSup_option
-/
theorem iSup_option_elim (a : α) (f : β -> α) : ⨆ o : Option β, o.elim a f = a ⊔ ⨆ b, f b := by
  simp [iSup_option]

/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
@[to_dual /-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤`
can be dropped, without changing the result. -/, simp]
/--
theorem `iSup_ne_bot_subtype` / 定理 `iSup_ne_bot_subtype`

English:
theorem iSup_ne_bot_subtype
  given: (f : ι -> α)
  statement: ⨆ i : { i // f i != ⊥ }, f i = ⨆ i, f i
  proof: by
  by_cases! htriv : forall i, f i = ⊥
  · simp only [iSup_bot, (funext htriv : f = _)]
  refine (iSup_comp_le f _).antisymm (iSup_mono' fun i => ?_)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩

@[to_dual]

中文:
定理 iSup_ne_bot_subtype
  条件: (f : ι -> α)
  结论: ⨆ i : { i // f i != ⊥ }, f i = ⨆ i, f i
  证明: by
  by_cases! htriv : forall i, f i = ⊥
  · simp only [iSup_bot, (funext htriv : f = _)]
  refine (iSup_comp_le f _).antisymm (iSup_mono' fun i => ?_)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩

@[to_dual]

Depends on / 依赖: antisymm, bot_le, iSup_bot, iSup_comp_le, iSup_mono, rfl.le
-/
theorem iSup_ne_bot_subtype (f : ι -> α) : ⨆ i : { i // f i != ⊥ }, f i = ⨆ i, f i := by
  by_cases! htriv : forall i, f i = ⊥
  · simp only [iSup_bot, (funext htriv : f = _)]
  refine (iSup_comp_le f _).antisymm (iSup_mono' fun i => ?_)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩

@[to_dual]
/--
theorem `sSup_image2` / 定理 `sSup_image2`

English:
theorem sSup_image2
  given: {f : β -> γ -> α} {s : Set β} {t : Set γ}
  proof: by rw [← image_prod, sSup_image, biSup_prod]

中文:
定理 sSup_image2
  条件: {f : β -> γ -> α} {s : Set β} {t : Set γ}
  证明: by rw [← image_prod, sSup_image, biSup_prod]

Depends on / 依赖: biSup_prod, image_prod, sSup_image
-/
theorem sSup_image2 {f : β -> γ -> α} {s : Set β} {t : Set γ} :
    sSup (image2 f s t) = ⨆ (a in s) (b in t), f a b := by rw [← image_prod, sSup_image, biSup_prod]

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

@[to_dual]
/--
lemma `iSup₂_eq_top` / 引理 `iSup₂_eq_top`

English:
lemma iSup₂_eq_top
  given: (f : forall i, κ i -> α)
  statement: ⨆ i, ⨆ j, f i j = ⊤ ↔ forall b < ⊤, exists i j, b < f i j
  proof: by
  simp_rw [iSup_psigma', iSup_eq_top, PSigma.exists]

中文:
引理 iSup₂_eq_top
  条件: (f : 对任意 i, κ i -> α)
  结论: ⨆ i, ⨆ j, f i j = ⊤ ↔ 对任意 b < ⊤, 存在 i j, b < f i j
  证明: by
  simp_rw [iSup_psigma', iSup_eq_top, PSigma.exists]

Depends on / 依赖: PSigma, PSigma.exists, iSup_eq_top, iSup_psigma, simp_rw
-/
lemma iSup₂_eq_top (f : forall i, κ i -> α) : ⨆ i, ⨆ j, f i j = ⊤ ↔ forall b < ⊤, exists i j, b < f i j := by
  simp_rw [iSup_psigma', iSup_eq_top, PSigma.exists]

end CompleteLinearOrder



/--
Instance `Prop.instCompleteLattice` / 实例 `Prop.instCompleteLattice`

English:
instance Prop.instCompleteLattice
  signature: : CompleteLattice Prop where
  body: Prop.instBoundedOrder
  __ := Prop.instDistribLattice
  sSup s := exists a in s, a
  isLUB_sSup _ := ⟨fun a h p => ⟨a, h, p⟩, fun _ h ⟨_, h', p⟩ => h h' p⟩
  sInf s := forall a in s, a
  isGLB_sInf _ := ⟨fun a h p => p a h, fun _ h p _ hb => h hb p⟩

中文:
实例 Prop.instCompleteLattice
  签名: : CompleteLattice 命题 where
  定义体: Prop.instBoundedOrder
  __ := Prop.instDistribLattice
  sSup s := exists a in s, a
  isLUB_sSup _ := ⟨fun a h p => ⟨a, h, p⟩, fun _ h ⟨_, h', p⟩ => h h' p⟩
  sInf s := forall a in s, a
  isGLB_sInf _ := ⟨fun a h p => p a h, fun _ h p _ hb => h hb p⟩

Depends on / 依赖: Prop.instBoundedOrder, instBoundedOrder
-/
instance Prop.instCompleteLattice : CompleteLattice Prop where
  __ := Prop.instBoundedOrder
  __ := Prop.instDistribLattice
  sSup s := exists a in s, a
  isLUB_sSup _ := ⟨fun a h p => ⟨a, h, p⟩, fun _ h ⟨_, h', p⟩ => h h' p⟩
  sInf s := forall a in s, a
  isGLB_sInf _ := ⟨fun a h p => p a h, fun _ h p _ hb => h hb p⟩

/--
Instance `Prop.instCompleteLinearOrder` / 实例 `Prop.instCompleteLinearOrder`

English:
instance Prop.instCompleteLinearOrder
  signature: : CompleteLinearOrder Prop where
  body: Prop.instCompleteLattice
  __ := Prop.linearOrder
  __ := BooleanAlgebra.toBiheytingAlgebra

@[simp]

中文:
实例 Prop.instCompleteLinearOrder
  签名: : CompleteLinearOrder 命题 where
  定义体: Prop.instCompleteLattice
  __ := Prop.linearOrder
  __ := BooleanAlgebra.toBiheytingAlgebra

@[simp]

Depends on / 依赖: Prop.instCompleteLattice, instCompleteLattice
-/
noncomputable instance Prop.instCompleteLinearOrder : CompleteLinearOrder Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.linearOrder
  __ := BooleanAlgebra.toBiheytingAlgebra

@[simp]
/--
theorem `sSup_Prop_eq` / 定理 `sSup_Prop_eq`

English:
theorem sSup_Prop_eq
  given: {s : Set Prop}
  statement: sSup s = exists p in s, p
  proof: rfl

@[simp]

中文:
定理 sSup_Prop_eq
  条件: {s : Set 命题}
  结论: sSup s = 存在 p in s, p
  证明: rfl

@[simp]
-/
theorem sSup_Prop_eq {s : Set Prop} : sSup s = exists p in s, p :=
  rfl

@[simp]
/--
theorem `sInf_Prop_eq` / 定理 `sInf_Prop_eq`

English:
theorem sInf_Prop_eq
  given: {s : Set Prop}
  statement: sInf s = forall p in s, p
  proof: rfl

@[simp]

中文:
定理 sInf_Prop_eq
  条件: {s : Set 命题}
  结论: sInf s = 对任意 p in s, p
  证明: rfl

@[simp]
-/
theorem sInf_Prop_eq {s : Set Prop} : sInf s = forall p in s, p :=
  rfl

@[simp]
/--
theorem `iSup_Prop_eq` / 定理 `iSup_Prop_eq`

English:
theorem iSup_Prop_eq
  given: {p : ι -> Prop}
  statement: ⨆ i, p i = exists i, p i
  proof: le_antisymm (fun ⟨_, ⟨i, (eq : p i = _)⟩, hq⟩ => ⟨i, eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩

@[simp]

中文:
定理 iSup_Prop_eq
  条件: {p : ι -> 命题}
  结论: ⨆ i, p i = 存在 i, p i
  证明: le_antisymm (fun ⟨_, ⟨i, (eq : p i = _)⟩, hq⟩ => ⟨i, eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩

@[simp]

Depends on / 依赖: eq.symm, le_antisymm
-/
theorem iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i :=
  le_antisymm (fun ⟨_, ⟨i, (eq : p i = _)⟩, hq⟩ => ⟨i, eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩

@[simp]
/--
theorem `iInf_Prop_eq` / 定理 `iInf_Prop_eq`

English:
theorem iInf_Prop_eq
  given: {p : ι -> Prop}
  statement: ⨅ i, p i = forall i, p i
  proof: le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual]

中文:
定理 iInf_Prop_eq
  条件: {p : ι -> 命题}
  结论: ⨅ i, p i = 对任意 i, p i
  证明: le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual]

Depends on / 依赖: le_antisymm
-/
theorem iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i :=
  le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h _ ⟨i, Eq⟩ => Eq ▸ h i

@[to_dual]
/--
Instance `Pi.supSet` / 实例 `Pi.supSet`

English:
instance Pi.supSet
  signature: {α : Type*} {β : α -> Type*} [forall i, SupSet (β i)]
  body: ⟨fun s i => ⨆ f : s, (f : forall i, β i) i⟩

@[to_dual (attr := simp)]

中文:
实例 Pi.supSet
  签名: {α : 类型} {β : α -> 类型} [对任意 i, SupSet (β i)]
  定义体: ⟨fun s i => ⨆ f : s, (f : forall i, β i) i⟩

@[to_dual (attr := simp)]
-/
instance Pi.supSet {α : Type*} {β : α -> Type*} [forall i, SupSet (β i)] : SupSet (forall i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : forall i, β i) i⟩

@[to_dual (attr := simp)]
/--
theorem `sSup_apply` / 定理 `sSup_apply`

English:
theorem sSup_apply
  given: {α : Type*} {β : α -> Type*} [forall i, SupSet (β i)] {s : Set (forall a, β a)} {a : α}
  proof: rfl

@[to_dual]

中文:
定理 sSup_apply
  条件: {α : 类型} {β : α -> 类型} [对任意 i, SupSet (β i)] {s : Set (对任意 a, β a)} {a : α}
  证明: rfl

@[to_dual]
-/
theorem sSup_apply {α : Type*} {β : α -> Type*} [forall i, SupSet (β i)] {s : Set (forall a, β a)} {a : α} :
    (sSup s) a = ⨆ f : s, (f : forall a, β a) a :=
  rfl

@[to_dual]
/--
theorem `sSup_apply_eq_sSup_image` / 定理 `sSup_apply_eq_sSup_image`

English:
theorem sSup_apply_eq_sSup_image
  statement: {α : Type*} {β : α -> Type*} [forall i, SupSet (β i)]
  proof: by
  simp [sSup_apply, iSup, image_eq_range]

中文:
定理 sSup_apply_eq_sSup_image
  结论: {α : 类型} {β : α -> 类型} [对任意 i, SupSet (β i)]
  证明: by
  simp [sSup_apply, iSup, image_eq_range]

Depends on / 依赖: image_eq_range, sSup_apply
-/
theorem sSup_apply_eq_sSup_image {α : Type*} {β : α -> Type*} [forall i, SupSet (β i)]
    {s : Set (forall a, β a)} {a : α} :
    sSup s a = sSup (eval a '' s) := by
  simp [sSup_apply, iSup, image_eq_range]

/--
Instance `Pi.instCompleteLattice` / 实例 `Pi.instCompleteLattice`

English:
instance Pi.instCompleteLattice
  signature: {α : Type*} {β : α -> Type*} [forall i, CompleteLattice (β i)]
  body: instBoundedOrder
  isLUB_sSup _ := isLUB_pi.mpr fun _ => by rw [sSup_apply_eq_sSup_image]; exact isLUB_sSup _
  isGLB_sInf _ := isGLB_pi.mpr fun _ => by rw [sInf_apply_eq_sInf_image]; exact isGLB_sInf _

@[to_dual (attr := simp)]

中文:
实例 Pi.instCompleteLattice
  签名: {α : 类型} {β : α -> 类型} [对任意 i, CompleteLattice (β i)]
  定义体: instBoundedOrder
  isLUB_sSup _ := isLUB_pi.mpr fun _ => by rw [sSup_apply_eq_sSup_image]; exact isLUB_sSup _
  isGLB_sInf _ := isGLB_pi.mpr fun _ => by rw [sInf_apply_eq_sInf_image]; exact isGLB_sInf _

@[to_dual (attr := simp)]

Depends on / 依赖: instBoundedOrder
-/
instance Pi.instCompleteLattice {α : Type*} {β : α -> Type*} [forall i, CompleteLattice (β i)] :
    CompleteLattice (forall i, β i) where
  __ := instBoundedOrder
  isLUB_sSup _ := isLUB_pi.mpr fun _ => by rw [sSup_apply_eq_sSup_image]; exact isLUB_sSup _
  isGLB_sInf _ := isGLB_pi.mpr fun _ => by rw [sInf_apply_eq_sInf_image]; exact isGLB_sInf _

@[to_dual (attr := simp)]
/--
theorem `iSup_apply` / 定理 `iSup_apply`

English:
theorem iSup_apply
  statement: {α : Type*} {β : α -> Type*} {ι : Sort*} [forall i, SupSet (β i)] {f : ι -> forall a, β a}
  proof: by
  rw [iSup]; rw [sSup_apply]; rw [iSup]; rw [iSup]; rw [← image_eq_range (fun f : forall i]; rw [β i => f a) (range f)]; rw [←
    range_comp]; rfl

中文:
定理 iSup_apply
  结论: {α : 类型} {β : α -> 类型} {ι : Sort*} [对任意 i, SupSet (β i)] {f : ι -> 对任意 a, β a}
  证明: by
  rw [iSup]; rw [sSup_apply]; rw [iSup]; rw [iSup]; rw [← image_eq_range (fun f : forall i]; rw [β i => f a) (range f)]; rw [←
    range_comp]; rfl

Depends on / 依赖: image_eq_range, range_comp, sSup_apply
-/
theorem iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall i, SupSet (β i)] {f : ι -> forall a, β a}
    {a : α} : (⨆ i, f i) a = ⨆ i, f i a := by
  rw [iSup]; rw [sSup_apply]; rw [iSup]; rw [iSup]; rw [← image_eq_range (fun f : forall i]; rw [β i => f a) (range f)]; rw [←
    range_comp]; rfl

/--
theorem `unary_relation_sSup_iff` / 定理 `unary_relation_sSup_iff`

English:
theorem unary_relation_sSup_iff
  given: {α : Type*} (s : Set (α -> Prop)) {a : α}
  proof: by
  simp

中文:
定理 unary_relation_sSup_iff
  条件: {α : 类型} (s : Set (α -> 命题)) {a : α}
  证明: by
  simp
-/
theorem unary_relation_sSup_iff {α : Type*} (s : Set (α -> Prop)) {a : α} :
    sSup s a ↔ exists r in s, r a := by
  simp

/--
theorem `unary_relation_sInf_iff` / 定理 `unary_relation_sInf_iff`

English:
theorem unary_relation_sInf_iff
  given: {α : Type*} (s : Set (α -> Prop)) {a : α}
  proof: by
  simp

中文:
定理 unary_relation_sInf_iff
  条件: {α : 类型} (s : Set (α -> 命题)) {a : α}
  证明: by
  simp
-/
theorem unary_relation_sInf_iff {α : Type*} (s : Set (α -> Prop)) {a : α} :
    sInf s a ↔ forall r in s, r a := by
  simp

/--
theorem `binary_relation_sSup_iff` / 定理 `binary_relation_sSup_iff`

English:
theorem binary_relation_sSup_iff
  given: {α β : Type*} (s : Set (α -> β -> Prop)) {a : α} {b : β}
  proof: by
  simp

中文:
定理 binary_relation_sSup_iff
  条件: {α β : 类型} (s : Set (α -> β -> 命题)) {a : α} {b : β}
  证明: by
  simp
-/
theorem binary_relation_sSup_iff {α β : Type*} (s : Set (α -> β -> Prop)) {a : α} {b : β} :
    sSup s a b ↔ exists r in s, r a b := by
  simp

/--
theorem `binary_relation_sInf_iff` / 定理 `binary_relation_sInf_iff`

English:
theorem binary_relation_sInf_iff
  given: {α β : Type*} (s : Set (α -> β -> Prop)) {a : α} {b : β}
  proof: by
  simp

中文:
定理 binary_relation_sInf_iff
  条件: {α β : 类型} (s : Set (α -> β -> 命题)) {a : α} {b : β}
  证明: by
  simp
-/
theorem binary_relation_sInf_iff {α β : Type*} (s : Set (α -> β -> Prop)) {a : α} {b : β} :
    sInf s a b ↔ forall r in s, r a b := by
  simp

section CompleteLattice

variable [Preorder α] [CompleteLattice β] {s : Set (α -> β)} {f : ι -> α -> β}

@[to_dual]
/--
lemma `Monotone.sSup` / 引理 `Monotone.sSup`

English:
lemma Monotone.sSup
  given: (hs : forall f in s, Monotone f)
  statement: Monotone (sSup s)
  proof: fun _ _ h => iSup_mono fun f => hs f f.2 h

@[to_dual]

中文:
引理 Monotone.sSup
  条件: (hs : 对任意 f in s, Monotone f)
  结论: Monotone (sSup s)
  证明: fun _ _ h => iSup_mono fun f => hs f f.2 h

@[to_dual]
-/
protected lemma Monotone.sSup (hs : forall f in s, Monotone f) : Monotone (sSup s) :=
  fun _ _ h => iSup_mono fun f => hs f f.2 h

@[to_dual]
/--
lemma `Antitone.sSup` / 引理 `Antitone.sSup`

English:
lemma Antitone.sSup
  given: (hs : forall f in s, Antitone f)
  statement: Antitone (sSup s)
  proof: fun _ _ h => iSup_mono fun f => hs f f.2 h

@[to_dual]

中文:
引理 Antitone.sSup
  条件: (hs : 对任意 f in s, Antitone f)
  结论: Antitone (sSup s)
  证明: fun _ _ h => iSup_mono fun f => hs f f.2 h

@[to_dual]
-/
protected lemma Antitone.sSup (hs : forall f in s, Antitone f) : Antitone (sSup s) :=
  fun _ _ h => iSup_mono fun f => hs f f.2 h

@[to_dual]
/--
lemma `Monotone.iSup` / 引理 `Monotone.iSup`

English:
lemma Monotone.iSup
  given: (hf : forall i, Monotone (f i))
  statement: Monotone (⨆ i, f i)
  proof: Monotone.sSup (by simpa)

@[to_dual]

中文:
引理 Monotone.iSup
  条件: (hf : 对任意 i, Monotone (f i))
  结论: Monotone (⨆ i, f i)
  证明: Monotone.sSup (by simpa)

@[to_dual]
-/
protected lemma Monotone.iSup (hf : forall i, Monotone (f i)) : Monotone (⨆ i, f i) :=
  Monotone.sSup (by simpa)

@[to_dual]
/--
lemma `Antitone.iSup` / 引理 `Antitone.iSup`

English:
lemma Antitone.iSup
  given: (hf : forall i, Antitone (f i))
  statement: Antitone (⨆ i, f i)
  proof: Antitone.sSup (by simpa)

中文:
引理 Antitone.iSup
  条件: (hf : 对任意 i, Antitone (f i))
  结论: Antitone (⨆ i, f i)
  证明: Antitone.sSup (by simpa)
-/
protected lemma Antitone.iSup (hf : forall i, Antitone (f i)) : Antitone (⨆ i, f i) :=
  Antitone.sSup (by simpa)

end CompleteLattice

namespace Prod

variable (α β)

@[to_dual]
/--
Instance `supSet` / 实例 `supSet`

English:
instance supSet
  signature: [SupSet α] [SupSet β]
  body: ⟨fun s => (sSup (Prod.fst '' s), sSup (Prod.snd '' s))⟩

中文:
实例 supSet
  签名: [SupSet α] [SupSet β]
  定义体: ⟨fun s => (sSup (Prod.fst '' s), sSup (Prod.snd '' s))⟩

Depends on / 依赖: Prod.fst, Prod.snd
-/
instance supSet [SupSet α] [SupSet β] : SupSet (α × β) :=
  ⟨fun s => (sSup (Prod.fst '' s), sSup (Prod.snd '' s))⟩

variable {α β}

@[to_dual]
/--
theorem `fst_sSup` / 定理 `fst_sSup`

English:
theorem fst_sSup
  given: [SupSet α] [SupSet β] (s : Set (α × β))
  statement: (sSup s).fst = sSup (Prod.fst '' s)
  proof: rfl

@[to_dual]

中文:
定理 fst_sSup
  条件: [SupSet α] [SupSet β] (s : Set (α × β))
  结论: (sSup s).fst = sSup (Prod.fst '' s)
  证明: rfl

@[to_dual]
-/
theorem fst_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).fst = sSup (Prod.fst '' s) :=
  rfl

@[to_dual]
/--
theorem `snd_sSup` / 定理 `snd_sSup`

English:
theorem snd_sSup
  given: [SupSet α] [SupSet β] (s : Set (α × β))
  statement: (sSup s).snd = sSup (Prod.snd '' s)
  proof: rfl

@[to_dual]

中文:
定理 snd_sSup
  条件: [SupSet α] [SupSet β] (s : Set (α × β))
  结论: (sSup s).snd = sSup (Prod.snd '' s)
  证明: rfl

@[to_dual]
-/
theorem snd_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).snd = sSup (Prod.snd '' s) :=
  rfl

@[to_dual]
/--
theorem `swap_sSup` / 定理 `swap_sSup`

English:
theorem swap_sSup
  given: [SupSet α] [SupSet β] (s : Set (α × β))
  statement: (sSup s).swap = sSup (Prod.swap '' s)
  proof: Prod.ext (congr_arg sSup <| image_comp Prod.fst swap s)
    (congr_arg sSup <| image_comp Prod.snd swap s)

@[to_dual]

中文:
定理 swap_sSup
  条件: [SupSet α] [SupSet β] (s : Set (α × β))
  结论: (sSup s).swap = sSup (Prod.swap '' s)
  证明: Prod.ext (congr_arg sSup <| image_comp Prod.fst swap s)
    (congr_arg sSup <| image_comp Prod.snd swap s)

@[to_dual]

Depends on / 依赖: Prod.ext, Prod.fst, Prod.snd, congr_arg, image_comp
-/
theorem swap_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).swap = sSup (Prod.swap '' s) :=
  Prod.ext (congr_arg sSup <| image_comp Prod.fst swap s)
    (congr_arg sSup <| image_comp Prod.snd swap s)

@[to_dual]
/--
theorem `fst_iSup` / 定理 `fst_iSup`

English:
theorem fst_iSup
  given: [SupSet α] [SupSet β] (f : ι -> α × β)
  statement: (iSup f).fst = ⨆ i, (f i).fst
  proof: congr_arg sSup (range_comp _ _).symm

@[to_dual]

中文:
定理 fst_iSup
  条件: [SupSet α] [SupSet β] (f : ι -> α × β)
  结论: (iSup f).fst = ⨆ i, (f i).fst
  证明: congr_arg sSup (range_comp _ _).symm

@[to_dual]

Depends on / 依赖: congr_arg, range_comp
-/
theorem fst_iSup [SupSet α] [SupSet β] (f : ι -> α × β) : (iSup f).fst = ⨆ i, (f i).fst :=
  congr_arg sSup (range_comp _ _).symm

@[to_dual]
/--
theorem `snd_iSup` / 定理 `snd_iSup`

English:
theorem snd_iSup
  given: [SupSet α] [SupSet β] (f : ι -> α × β)
  statement: (iSup f).snd = ⨆ i, (f i).snd
  proof: congr_arg sSup (range_comp _ _).symm

@[to_dual]

中文:
定理 snd_iSup
  条件: [SupSet α] [SupSet β] (f : ι -> α × β)
  结论: (iSup f).snd = ⨆ i, (f i).snd
  证明: congr_arg sSup (range_comp _ _).symm

@[to_dual]

Depends on / 依赖: congr_arg, range_comp
-/
theorem snd_iSup [SupSet α] [SupSet β] (f : ι -> α × β) : (iSup f).snd = ⨆ i, (f i).snd :=
  congr_arg sSup (range_comp _ _).symm

@[to_dual]
/--
theorem `swap_iSup` / 定理 `swap_iSup`

English:
theorem swap_iSup
  given: [SupSet α] [SupSet β] (f : ι -> α × β)
  statement: (iSup f).swap = ⨆ i, (f i).swap
  proof: by
  simp_rw [iSup, swap_sSup, ← range_comp, comp_def]

@[to_dual]

中文:
定理 swap_iSup
  条件: [SupSet α] [SupSet β] (f : ι -> α × β)
  结论: (iSup f).swap = ⨆ i, (f i).swap
  证明: by
  simp_rw [iSup, swap_sSup, ← range_comp, comp_def]

@[to_dual]

Depends on / 依赖: comp_def, range_comp, simp_rw, swap_sSup
-/
theorem swap_iSup [SupSet α] [SupSet β] (f : ι -> α × β) : (iSup f).swap = ⨆ i, (f i).swap := by
  simp_rw [iSup, swap_sSup, ← range_comp, comp_def]

@[to_dual]
/--
theorem `iSup_mk` / 定理 `iSup_mk`

English:
theorem iSup_mk
  given: [SupSet α] [SupSet β] (f : ι -> α) (g : ι -> β)
  proof: congr_arg₂ Prod.mk (fst_iSup _) (snd_iSup _)

中文:
定理 iSup_mk
  条件: [SupSet α] [SupSet β] (f : ι -> α) (g : ι -> β)
  证明: congr_arg₂ Prod.mk (fst_iSup _) (snd_iSup _)

Depends on / 依赖: Prod.mk, fst_iSup, snd_iSup
-/
theorem iSup_mk [SupSet α] [SupSet β] (f : ι -> α) (g : ι -> β) :
    ⨆ i, (f i, g i) = (⨆ i, f i, ⨆ i, g i) :=
  congr_arg₂ Prod.mk (fst_iSup _) (snd_iSup _)

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: [CompleteLattice α] [CompleteLattice β]
  body: instBoundedOrder α β
  isLUB_sSup _ := isLUB_prod.mpr ⟨isLUB_sSup _, isLUB_sSup _⟩
  isGLB_sInf _ := isGLB_prod.mpr ⟨isGLB_sInf _, isGLB_sInf _⟩

中文:
实例 instCompleteLattice
  签名: [CompleteLattice α] [CompleteLattice β]
  定义体: instBoundedOrder α β
  isLUB_sSup _ := isLUB_prod.mpr ⟨isLUB_sSup _, isLUB_sSup _⟩
  isGLB_sInf _ := isGLB_prod.mpr ⟨isGLB_sInf _, isGLB_sInf _⟩

Depends on / 依赖: instBoundedOrder
-/
instance instCompleteLattice [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) where
  __ := instBoundedOrder α β
  isLUB_sSup _ := isLUB_prod.mpr ⟨isLUB_sSup _, isLUB_sSup _⟩
  isGLB_sInf _ := isGLB_prod.mpr ⟨isGLB_sInf _, isGLB_sInf _⟩

end Prod

@[to_dual]
/--
lemma `sSup_prod` / 引理 `sSup_prod`

English:
lemma sSup_prod
  given: [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty)
  proof: congr_arg₂ Prod.mk (congr_arg sSup <| fst_image_prod _ ht) (congr_arg sSup <| snd_image_prod hs _)

中文:
引理 sSup_prod
  条件: [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty)
  证明: congr_arg₂ Prod.mk (congr_arg sSup <| fst_image_prod _ ht) (congr_arg sSup <| snd_image_prod hs _)

Depends on / 依赖: Prod.mk, congr_arg, fst_image_prod, snd_image_prod
-/
lemma sSup_prod [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty) :
    sSup (s ×ˢ t) = (sSup s, sSup t) :=
congr_arg₂ Prod.mk (congr_arg sSup <| fst_image_prod _ ht) (congr_arg sSup <| snd_image_prod hs _)

-- See note [reducible non-instances]
/--
Definition of `Function.Injective.completeLattice` / `Function.Injective.completeLattice` 的定义

English:
abbreviation Function.Injective.completeLattice
  signature: [Max α] [Min α] [LE α] [LT α]
  body: hf.lattice f le lt map_sup map_inf
  __ := BoundedOrder.lift f (fun _ _ => le.1) map_top map_bot
  isLUB_sSup _ := .of_image le (by rw [map_sSup]; exact isLUB_biSup)
  isGLB_sInf _ := .of_image le (by rw [map_sInf]; exact isGLB_biInf)

中文:
缩写 Function.Injective.completeLattice
  签名: [Max α] [Min α] [LE α] [LT α]
  定义体: hf.lattice f le lt map_sup map_inf
  __ := BoundedOrder.lift f (fun _ _ => le.1) map_top map_bot
  isLUB_sSup _ := .of_image le (by rw [map_sSup]; exact isLUB_biSup)
  isGLB_sInf _ := .of_image le (by rw [map_sInf]; exact isGLB_biInf)
-/
protected abbrev Function.Injective.completeLattice [Max α] [Min α] [LE α] [LT α]
    [SupSet α] [InfSet α] [Top α] [Bot α] [CompleteLattice β]
    (f : α -> β) (hf : Function.Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (map_sup : forall a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : forall a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : forall s, f (sSup s) = ⨆ a in s, f a) (map_sInf : forall s, f (sInf s) = ⨅ a in s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α where
  __ := hf.lattice f le lt map_sup map_inf
  __ := BoundedOrder.lift f (fun _ _ => le.1) map_top map_bot
  isLUB_sSup _ := .of_image le (by rw [map_sSup]; exact isLUB_biSup)
  isGLB_sInf _ := .of_image le (by rw [map_sInf]; exact isGLB_biInf)

namespace Equiv

variable (e : α ≃ β)

/--
Definition of `completeLattice` / `completeLattice` 的定义

English:
abbreviation completeLattice
  signature: [CompleteLattice β]
  body: by
  let top := e.top
  let bot := e.bot
  let supSet := e.supSet
  let infSet := e.infSet
  let lattice := e.lattice
  apply e.injective.completeLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

中文:
缩写 completeLattice
  签名: [CompleteLattice β]
  定义体: by
  let top := e.top
  let bot := e.bot
  let supSet := e.supSet
  let infSet := e.infSet
  let lattice := e.lattice
  apply e.injective.completeLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _
-/
protected abbrev completeLattice [CompleteLattice β] : CompleteLattice α := by
  let top := e.top
  let bot := e.bot
  let supSet := e.supSet
  let infSet := e.infSet
  let lattice := e.lattice
  apply e.injective.completeLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv
