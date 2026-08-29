/-
Copyright (c) 2025 Finn Mortimore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Finn Mortimore
-/
module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Data.Set.Lattice
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Bourbaki-Witt Theorem

This file proves the Bourbaki-Witt Theorem.

## Main definitions

- class `ChainCompletePartialOrder` : A nonempty partial order is a chain complete partial order
  such that every nonempty chain has a supremum

## Main statements

- `nonempty_fixedPoints_of_inflationary` : The Bourbaki-Witt Theorem : If $X$ is a chain complete
  partial order and $f : X → X$ is inflationary (i.e. ∀ x, x ≤ f x), then $f$ has a fixed point

## References

The proof used can be found in [serge_lang_algebra]
-/

public section

variable {α β : Type*} {ι : Sort*}

/-- The type of nonempty chains of an order -/
@[ext]
/--
Definition of `NonemptyChain` / `NonemptyChain` 的定义

English:
structure NonemptyChain
  parameters: (α : Type*) [LE α]
  axioms and operations (3):
    - carrier : Set α
    - Nonempty' : carrier.Nonempty
    - isChain' : IsChain (· <= ·) carrier

中文:
结构 NonemptyChain
  参数: (α : 类型) [LE α]
  公理与运算 (3 个):
    - carrier : Set α
    - Nonempty' : carrier.Nonempty
    - isChain' : IsChain (· <= ·) carrier
-/
structure NonemptyChain (α : Type*) [LE α] where
  /-- The underlying set of a nonempty chain -/
  carrier : Set α
  Nonempty' : carrier.Nonempty
  isChain' : IsChain (· <= ·) carrier

instance {α : Type*} [LE α] : SetLike (NonemptyChain α) α where
  coe := NonemptyChain.carrier
  coe_injective _ _ := NonemptyChain.ext

instance {α : Type*} [LE α] : PartialOrder (NonemptyChain α) := .ofSetLike (NonemptyChain α) α

/--
Definition of `ChainCompletePartialOrder` / `ChainCompletePartialOrder` 的定义

English:
class ChainCompletePartialOrder
  parameters: (α : Type*)
  extends: PartialOrder α
  axioms and operations (3):
    - cSup : NonemptyChain α -> α
    - le_cSup((c : NonemptyChain α) (x : α)) : x in c.carrier -> x <= cSup c
    - cSup_le((c : NonemptyChain α) (x : α)) : (forall y in c.carrier, y <= x) -> cSup c <= x

中文:
类 ChainCompletePartialOrder
  参数: (α : 类型)
  继承: PartialOrder α
  公理与运算 (3 个):
    - cSup : NonemptyChain α -> α
    - le_cSup((c : NonemptyChain α) (x : α)) : x in c.carrier -> x <= cSup c
    - cSup_le((c : NonemptyChain α) (x : α)) : (对任意 y in c.carrier, y <= x) -> cSup c <= x
-/
class ChainCompletePartialOrder (α : Type*) extends PartialOrder α where
  /-- The supremum of a nonempty chain -/
  cSup : NonemptyChain α -> α
  /-- `cSup` is an upper bound of the nonempty chain -/
  le_cSup (c : NonemptyChain α) (x : α) : x in c.carrier -> x <= cSup c
  /-- `cSup` is a lower bound of the set of upper bounds of the nonempty chain -/
  cSup_le (c : NonemptyChain α) (x : α) : (forall y in c.carrier, y <= x) -> cSup c <= x

open ChainCompletePartialOrder Set OmegaCompletePartialOrder.Chain

namespace ChainCompletePartialOrder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ChainCompletePartialOrder
  signature: α] : OmegaCompletePartialOrder α where
  body: cSup (NonemptyChain.mk (range c) (range_nonempty c) (isChain_range c))
  le_ωSup _ i := le_cSup _ _ (mem_range_self i)
  ωSup_le _ _ hx := cSup_le _ _ (fun _ ⟨i, hi⟩ => hi ▸ hx i)

中文:
实例 [ChainCompletePartialOrder
  签名: α] : OmegaCompletePartialOrder α where
  定义体: cSup (NonemptyChain.mk (range c) (range_nonempty c) (isChain_range c))
  le_ωSup _ i := le_cSup _ _ (mem_range_self i)
  ωSup_le _ _ hx := cSup_le _ _ (fun _ ⟨i, hi⟩ => hi ▸ hx i)

Depends on / 依赖: NonemptyChain, NonemptyChain.mk, isChain_range, range_nonempty
-/
instance [ChainCompletePartialOrder α] : OmegaCompletePartialOrder α where
  ωSup c := cSup (NonemptyChain.mk (range c) (range_nonempty c) (isChain_range c))
  le_ωSup _ i := le_cSup _ _ (mem_range_self i)
  ωSup_le _ _ hx := cSup_le _ _ (fun _ ⟨i, hi⟩ => hi ▸ hx i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteLattice
  signature: α] : ChainCompletePartialOrder α where
  body: sSup c
  le_cSup _ _ hx := le_sSup hx
  cSup_le _ _ h := sSup_le h

中文:
实例 [CompleteLattice
  签名: α] : ChainCompletePartialOrder α where
  定义体: sSup c
  le_cSup _ _ hx := le_sSup hx
  cSup_le _ _ h := sSup_le h
-/
instance [CompleteLattice α] : ChainCompletePartialOrder α where
  cSup c := sSup c
  le_cSup _ _ hx := le_sSup hx
  cSup_le _ _ h := sSup_le h

variable [ChainCompletePartialOrder α] {x : α} {f : α -> α}

/--
Definition of `IsAdmissible` / `IsAdmissible` 的定义

English:
structure IsAdmissible
  parameters: (x : α) (f : α -> α) (s : Set α)
  axioms and operations (3):
    - base_isLeast : IsLeast s x
    - image_self_subset_self : f '' s subseteq s
    - cSup_mem : forall (c : NonemptyChain α), ↑c subseteq s -> cSup c in s

中文:
结构 IsAdmissible
  参数: (x : α) (f : α -> α) (s : Set α)
  公理与运算 (3 个):
    - base_isLeast : IsLeast s x
    - image_self_subset_self : f '' s subseteq s
    - cSup_mem : 对任意 (c : NonemptyChain α), ↑c subseteq s -> cSup c in s
-/
structure IsAdmissible (x : α) (f : α -> α) (s : Set α) : Prop where
  /-- The base point is the least element of an admissible set -/
  base_isLeast : IsLeast s x
  /-- The image of an admissible set under `f` is a subset of itself -/
  image_self_subset_self : f '' s subseteq s
  /-- If a chain is a subset of an admissible set, its `cSup` is a member of the admissible set -/
  cSup_mem : forall (c : NonemptyChain α), ↑c subseteq s -> cSup c in s

/--
lemma `ici_isAdmissible` / 引理 `ici_isAdmissible`

English:
lemma ici_isAdmissible
  given: (le_map : forall x, x <= f x)
  statement: IsAdmissible x f (Ici x) where
  proof: ⟨le_refl x, fun _ h => h⟩
  image_self_subset_self := by
    rintro _ ⟨y, hy, rfl⟩
    exact le_trans hy (le_map _)
  cSup_mem := by
    intro c hc
    have ⟨y, hy⟩ := c.Nonempty'
    exact le_trans (hc hy) (le_cSup _ _ hy)

中文:
引理 ici_isAdmissible
  条件: (le_map : 对任意 x, x <= f x)
  结论: IsAdmissible x f (Ici x) where
  证明: ⟨le_refl x, fun _ h => h⟩
  image_self_subset_self := by
    rintro _ ⟨y, hy, rfl⟩
    exact le_trans hy (le_map _)
  cSup_mem := by
    intro c hc
    have ⟨y, hy⟩ := c.Nonempty'
    exact le_trans (hc hy) (le_cSup _ _ hy)

Depends on / 依赖: le_refl
-/
lemma ici_isAdmissible (le_map : forall x, x <= f x) : IsAdmissible x f (Ici x) where
  base_isLeast := ⟨le_refl x, fun _ h => h⟩
  image_self_subset_self := by
    rintro _ ⟨y, hy, rfl⟩
    exact le_trans hy (le_map _)
  cSup_mem := by
    intro c hc
    have ⟨y, hy⟩ := c.Nonempty'
    exact le_trans (hc hy) (le_cSup _ _ hy)

/--
Definition of `bot` / `bot` 的定义

English:
abbreviation bot
  signature: (x : α) (f : α -> α)
  body: ⋂₀ {s | IsAdmissible x f s}

中文:
缩写 bot
  签名: (x : α) (f : α -> α)
  定义体: ⋂₀ {s | IsAdmissible x f s}

Depends on / 依赖: IsAdmissible
-/
abbrev bot (x : α) (f : α -> α) : Set α := ⋂₀ {s | IsAdmissible x f s}

/--
lemma `bot_isAdmissible` / 引理 `bot_isAdmissible`

English:
lemma bot_isAdmissible
  given: (le_map : forall x, x <= f x)
  statement: IsAdmissible x f (bot x f) where
  proof: by
    constructor
    · exact fun _ h => h.base_isLeast.1
    · intro y hy
      exact hy (Ici x) (ici_isAdmissible le_map)
  image_self_subset_self := by
    rintro _ ⟨y, hy, rfl⟩ s hs
    exact hs.image_self_subset_self ⟨y, ⟨mem_sInter.1 hy _ hs, rfl⟩⟩
  cSup_mem := by
    intro c hc s hs
    exa

中文:
引理 bot_isAdmissible
  条件: (le_map : 对任意 x, x <= f x)
  结论: IsAdmissible x f (bot x f) where
  证明: by
    constructor
    · exact fun _ h => h.base_isLeast.1
    · intro y hy
      exact hy (Ici x) (ici_isAdmissible le_map)
  image_self_subset_self := by
    rintro _ ⟨y, hy, rfl⟩ s hs
    exact hs.image_self_subset_self ⟨y, ⟨mem_sInter.1 hy _ hs, rfl⟩⟩
  cSup_mem := by
    intro c hc s hs
    exa

Depends on / 依赖: base_isLeast, cSup_mem, h.base_isLeast, hs.cSup_mem, hs.image_self_subset_self, ici_isAdmissible, image_self_subset_self, le_map, mem_sInter, sInter_subset_of_mem, subset_trans
-/
lemma bot_isAdmissible (le_map : forall x, x <= f x) : IsAdmissible x f (bot x f) where
  base_isLeast := by
    constructor
    · exact fun _ h => h.base_isLeast.1
    · intro y hy
      exact hy (Ici x) (ici_isAdmissible le_map)
  image_self_subset_self := by
    rintro _ ⟨y, hy, rfl⟩ s hs
    exact hs.image_self_subset_self ⟨y, ⟨mem_sInter.1 hy _ hs, rfl⟩⟩
  cSup_mem := by
    intro c hc s hs
    exact hs.cSup_mem c (subset_trans hc (sInter_subset_of_mem hs))

/--
lemma `subset_bot_iff` / 引理 `subset_bot_iff`

English:
lemma subset_bot_iff
  given: {s : Set α} (h : IsAdmissible x f s)
  statement: s subseteq bot x f ↔ s = bot x f where
  proof: subset_antisymm h' (sInter_subset_of_mem h)
  mpr h' := h' ▸ subset_refl (bot x f)

中文:
引理 subset_bot_iff
  条件: {s : Set α} (h : IsAdmissible x f s)
  结论: s subseteq bot x f ↔ s = bot x f where
  证明: subset_antisymm h' (sInter_subset_of_mem h)
  mpr h' := h' ▸ subset_refl (bot x f)

Depends on / 依赖: sInter_subset_of_mem, subset_antisymm
-/
lemma subset_bot_iff {s : Set α} (h : IsAdmissible x f s) : s subseteq bot x f ↔ s = bot x f where
  mp h' := subset_antisymm h' (sInter_subset_of_mem h)
  mpr h' := h' ▸ subset_refl (bot x f)

/--
lemma `map_mem_bot` / 引理 `map_mem_bot`

English:
lemma map_mem_bot
  given: {y : α} (le_map : forall x, x <= f x) (h : y in bot x f)
  statement: f y in bot x f
  proof: (bot_isAdmissible le_map).image_self_subset_self mem_image_of_mem f h

中文:
引理 map_mem_bot
  条件: {y : α} (le_map : 对任意 x, x <= f x) (h : y in bot x f)
  结论: f y in bot x f
  证明: (bot_isAdmissible le_map).image_self_subset_self mem_image_of_mem f h

Depends on / 依赖: bot_isAdmissible, image_self_subset_self, le_map, mem_image_of_mem
-/
lemma map_mem_bot {y : α} (le_map : forall x, x <= f x) (h : y in bot x f) : f y in bot x f :=
(bot_isAdmissible le_map).image_self_subset_self mem_image_of_mem f h

/--
Definition of `IsExtremePt` / `IsExtremePt` 的定义

English:
structure IsExtremePt
  parameters: (x : α) (f : α -> α) (y : α)
  axioms and operations (2):
    - mem_bot : y in bot x f
    - map_le_of_mem_of_lt({z : α} (h : z in bot x f) (h' : z < y)) : f z <= y

中文:
结构 IsExtremePt
  参数: (x : α) (f : α -> α) (y : α)
  公理与运算 (2 个):
    - mem_bot : y in bot x f
    - map_le_of_mem_of_lt({z : α} (h : z in bot x f) (h' : z < y)) : f z <= y
-/
structure IsExtremePt (x : α) (f : α -> α) (y : α) : Prop where
  mem_bot : y in bot x f
  map_le_of_mem_of_lt {z : α} (h : z in bot x f) (h' : z < y) : f z <= y

namespace IsExtremePt

/--
lemma `bot_eq_of_le_or_map_le` / 引理 `bot_eq_of_le_or_map_le`

English:
lemma bot_eq_of_le_or_map_le
  given: {y : α} (le_map : forall x, x <= f x) (hy : IsExtremePt x f y)
  proof: by
  rw [← subset_bot_iff]
  · apply sep_subset
  · apply IsAdmissible.mk
    · constructor
      · constructor
        · exact (bot_isAdmissible le_map).base_isLeast.1
        · exact Or.inl ((bot_isAdmissible le_map).base_isLeast.2 hy.mem_bot)
      · exact fun y h => (bot_isAdmissible le_map).bas

中文:
引理 bot_eq_of_le_or_map_le
  条件: {y : α} (le_map : 对任意 x, x <= f x) (hy : IsExtremePt x f y)
  证明: by
  rw [← subset_bot_iff]
  · apply sep_subset
  · apply IsAdmissible.mk
    · constructor
      · constructor
        · exact (bot_isAdmissible le_map).base_isLeast.1
        · exact Or.inl ((bot_isAdmissible le_map).base_isLeast.2 hy.mem_bot)
      · exact fun y h => (bot_isAdmissible le_map).bas

Depends on / 依赖: IsAdmissible, IsAdmissible.mk, Or.inl, base_isLeast, bot_isAdmissible, hy.map_le_of_mem_of_lt, hy.mem_bot, le_iff_lt_or_eq, le_map, le_refl, le_trans, map_le_of_mem_of_lt, map_mem_bot, mem_bot, sep_subset, subset_bot_iff
-/
lemma bot_eq_of_le_or_map_le {y : α} (le_map : forall x, x <= f x) (hy : IsExtremePt x f y) :
    {z in bot x f | z <= y ∨ f y <= z} = bot x f := by
  rw [← subset_bot_iff]
  · apply sep_subset
  · apply IsAdmissible.mk
    · constructor
      · constructor
        · exact (bot_isAdmissible le_map).base_isLeast.1
        · exact Or.inl ((bot_isAdmissible le_map).base_isLeast.2 hy.mem_bot)
      · exact fun y h => (bot_isAdmissible le_map).base_isLeast.2 h.1
    · rintro _ ⟨z, ⟨hz, (hzy | hyz)⟩, rfl⟩ <;>
        refine ⟨map_mem_bot le_map hz, ?_⟩
      · rcases le_iff_lt_or_eq.1 hzy with (hzy | rfl)
        · left; exact hy.map_le_of_mem_of_lt hz hzy
        · right; exact le_refl _
      · right; exact le_trans hyz (le_map z)
    · intro c hc
      refine ⟨(bot_isAdmissible le_map).cSup_mem _ (subset_trans hc (sep_subset _ _)), ?_⟩
      · by_cases! h : forall z in c, z <= y
        · left; apply cSup_le c y h
        · rcases h with ⟨z, hz, hzy⟩
          have h' := Or.resolve_left (hc hz).2 hzy
          right
          apply le_trans h' (le_cSup _ _ hz)

/--
lemma `setOfPred_isExtremePt_isAdmissible` / 引理 `setOfPred_isExtremePt_isAdmissible`

English:
lemma setOfPred_isExtremePt_isAdmissible
  given: (le_map : forall x, x <= f x)
  proof: by
  apply IsAdmissible.mk
  · constructor
    · refine ⟨(bot_isAdmissible le_map).base_isLeast.1, ?_⟩
      intro y hy hyx
      exfalso
      exact lt_irrefl x (lt_of_le_of_lt ((bot_isAdmissible le_map).base_isLeast.2 hy) hyx)
    · exact fun y h => (bot_isAdmissible le_map).base_isLeast.2 h.1
  ·

中文:
引理 setOfPred_isExtremePt_isAdmissible
  条件: (le_map : 对任意 x, x <= f x)
  证明: by
  apply IsAdmissible.mk
  · constructor
    · refine ⟨(bot_isAdmissible le_map).base_isLeast.1, ?_⟩
      intro y hy hyx
      exfalso
      exact lt_irrefl x (lt_of_le_of_lt ((bot_isAdmissible le_map).base_isLeast.2 hy) hyx)
    · exact fun y h => (bot_isAdmissible le_map).base_isLeast.2 h.1
  ·

Depends on / 依赖: IsAdmissible, IsAdmissible.mk, base_isLeast, bot_eq_of_le_or_map_le, bot_isAdmissible, hy.mem_bot, le_iff_lt_or_eq, le_map, lt_irrefl, lt_of_le_of_lt, map_mem_bot, mem_bot
-/
lemma setOfPred_isExtremePt_isAdmissible (le_map : forall x, x <= f x) :
    IsAdmissible x f {y | IsExtremePt x f y} := by
  apply IsAdmissible.mk
  · constructor
    · refine ⟨(bot_isAdmissible le_map).base_isLeast.1, ?_⟩
      intro y hy hyx
      exfalso
      exact lt_irrefl x (lt_of_le_of_lt ((bot_isAdmissible le_map).base_isLeast.2 hy) hyx)
    · exact fun y h => (bot_isAdmissible le_map).base_isLeast.2 h.1
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨map_mem_bot le_map hy.mem_bot, ?_⟩
    intro z hz hzy
    have hz' := hz
    rw [← bot_eq_of_le_or_map_le le_map hy] at hz'
    rcases hz' with ⟨_, (hz' | hz')⟩
    · rcases le_iff_lt_or_eq.1 hz' with (hz' | rfl)
      · exact le_trans (hy.map_le_of_mem_of_lt hz hz') (le_map y)
      · exact le_refl (f z)
    · exfalso
      exact lt_irrefl z (lt_of_lt_of_le hzy hz')
  · intro c hc
    refine ⟨(bot_isAdmissible le_map).cSup_mem _ (subset_trans hc (fun _ h => h.mem_bot)), ?_⟩
    intro y hy hy'
    obtain ⟨z, hz, hzy⟩ : exists z in c, ¬ (f z <= y) := by
      by_contra! h
      apply lt_irrefl y (lt_of_lt_of_le hy' ?_)
      apply cSup_le
      intro z hz
      exact le_trans (le_map z) (h z hz)
    have h : y <= z := by
      rw [← bot_eq_of_le_or_map_le le_map (hc hz)] at hy
      exact Or.resolve_right hy.2 hzy
    obtain hyz | rfl := le_iff_lt_or_eq.1 h
    · exact le_trans ((hc hz).map_le_of_mem_of_lt hy hyz) (le_cSup _ _ hz)
    · have hc' := (bot_isAdmissible le_map).cSup_mem _ (subset_trans hc fun _ h => h.mem_bot)
      rw [← bot_eq_of_le_or_map_le le_map (hc hz)] at hc'
      apply hc'.2.resolve_left
      intro hc'
      exact lt_irrefl y (lt_of_lt_of_le hy' hc')

@[deprecated (since := "2026-07-09")]
alias setOf_isExtremePt_isAdmissible := setOfPred_isExtremePt_isAdmissible

/--
lemma `setOfPred_isExtremePt_eq_bot` / 引理 `setOfPred_isExtremePt_eq_bot`

English:
lemma setOfPred_isExtremePt_eq_bot
  given: (le_map : forall x, x <= f x)
  statement: {y | IsExtremePt x f y} = bot x f
  proof: by
  rw [← subset_bot_iff]
  · exact fun _ h => h.mem_bot
  · exact setOfPred_isExtremePt_isAdmissible le_map

@[deprecated (since := "2026-07-09")]
alias setOf_isExtremePt_eq_bot := setOfPred_isExtremePt_eq_bot

中文:
引理 setOfPred_isExtremePt_eq_bot
  条件: (le_map : 对任意 x, x <= f x)
  结论: {y | IsExtremePt x f y} = bot x f
  证明: by
  rw [← subset_bot_iff]
  · exact fun _ h => h.mem_bot
  · exact setOfPred_isExtremePt_isAdmissible le_map

@[deprecated (since := "2026-07-09")]
alias setOf_isExtremePt_eq_bot := setOfPred_isExtremePt_eq_bot

Depends on / 依赖: h.mem_bot, le_map, mem_bot, setOfPred_isExtremePt_isAdmissible, subset_bot_iff
-/
lemma setOfPred_isExtremePt_eq_bot (le_map : forall x, x <= f x) : {y | IsExtremePt x f y} = bot x f := by
  rw [← subset_bot_iff]
  · exact fun _ h => h.mem_bot
  · exact setOfPred_isExtremePt_isAdmissible le_map

@[deprecated (since := "2026-07-09")]
alias setOf_isExtremePt_eq_bot := setOfPred_isExtremePt_eq_bot

/--
lemma `mem_bot_iff_isExtremePt` / 引理 `mem_bot_iff_isExtremePt`

English:
lemma mem_bot_iff_isExtremePt
  given: {y : α} (le_map : forall x, x <= f x)
  proof: by
  rw [← setOfPred_isExtremePt_eq_bot le_map]; rw [mem_ofPred]

中文:
引理 mem_bot_iff_isExtremePt
  条件: {y : α} (le_map : 对任意 x, x <= f x)
  证明: by
  rw [← setOfPred_isExtremePt_eq_bot le_map]; rw [mem_ofPred]

Depends on / 依赖: le_map, mem_ofPred, setOfPred_isExtremePt_eq_bot
-/
lemma mem_bot_iff_isExtremePt {y : α} (le_map : forall x, x <= f x) :
    y in bot x f ↔ IsExtremePt x f y := by
  rw [← setOfPred_isExtremePt_eq_bot le_map]; rw [mem_ofPred]

/--
lemma `bot_isChain` / 引理 `bot_isChain`

English:
lemma bot_isChain
  given: (le_map : forall x, x <= f x)
  statement: IsChain (· <= ·) (bot x f)
  proof: by
  intro y hy z hz _
  rw [mem_bot_iff_isExtremePt le_map] at hy
  rw [← bot_eq_of_le_or_map_le le_map hy] at hz
  obtain ⟨_, (hz | hz)⟩ := hz
  · right; exact hz
  · left; exact le_trans (le_map y) hz

中文:
引理 bot_isChain
  条件: (le_map : 对任意 x, x <= f x)
  结论: IsChain (· <= ·) (bot x f)
  证明: by
  intro y hy z hz _
  rw [mem_bot_iff_isExtremePt le_map] at hy
  rw [← bot_eq_of_le_or_map_le le_map hy] at hz
  obtain ⟨_, (hz | hz)⟩ := hz
  · right; exact hz
  · left; exact le_trans (le_map y) hz

Depends on / 依赖: bot_eq_of_le_or_map_le, le_map, le_trans, mem_bot_iff_isExtremePt
-/
lemma bot_isChain (le_map : forall x, x <= f x) : IsChain (· <= ·) (bot x f) := by
  intro y hy z hz _
  rw [mem_bot_iff_isExtremePt le_map] at hy
  rw [← bot_eq_of_le_or_map_le le_map hy] at hz
  obtain ⟨_, (hz | hz)⟩ := hz
  · right; exact hz
  · left; exact le_trans (le_map y) hz

end IsExtremePt

open Function IsExtremePt

/--
theorem `nonempty_fixedPoints_of_inflationary` / 定理 `nonempty_fixedPoints_of_inflationary`

English:
theorem nonempty_fixedPoints_of_inflationary
  given: [Nonempty α] (le_map : forall x, x <= f x)
  proof: by
  let x : α := Classical.ofNonempty
  let y := cSup
    (NonemptyChain.mk (bot x f) ⟨x, (bot_isAdmissible le_map).base_isLeast.1⟩ (bot_isChain le_map))
  use y
  apply le_antisymm (le_cSup _ _ (_ : f y in bot x f)) (le_map y)
  apply (bot_isAdmissible le_map).image_self_subset_self
  use y
  exac

中文:
定理 nonempty_fixedPoints_of_inflationary
  条件: [Nonempty α] (le_map : 对任意 x, x <= f x)
  证明: by
  let x : α := Classical.ofNonempty
  let y := cSup
    (NonemptyChain.mk (bot x f) ⟨x, (bot_isAdmissible le_map).base_isLeast.1⟩ (bot_isChain le_map))
  use y
  apply le_antisymm (le_cSup _ _ (_ : f y in bot x f)) (le_map y)
  apply (bot_isAdmissible le_map).image_self_subset_self
  use y
  exac

Depends on / 依赖: Classical, Classical.ofNonempty, NonemptyChain, NonemptyChain.mk, base_isLeast, bot_isAdmissible, bot_isChain, cSup_mem, image_self_subset_self, le_antisymm, le_cSup, le_map, ofNonempty, subset_refl
-/
theorem nonempty_fixedPoints_of_inflationary [Nonempty α] (le_map : forall x, x <= f x) :
    (fixedPoints f).Nonempty := by
  let x : α := Classical.ofNonempty
  let y := cSup
    (NonemptyChain.mk (bot x f) ⟨x, (bot_isAdmissible le_map).base_isLeast.1⟩ (bot_isChain le_map))
  use y
  apply le_antisymm (le_cSup _ _ (_ : f y in bot x f)) (le_map y)
  apply (bot_isAdmissible le_map).image_self_subset_self
  use y
  exact ⟨(bot_isAdmissible le_map).cSup_mem _ (subset_refl _), rfl⟩

end ChainCompletePartialOrder

open OmegaCompletePartialOrder

namespace CompleteLattice

variable [OmegaCompletePartialOrder α] [CompleteLattice β] {f g : α -> β}

/--
lemma `ωScottContinuous.iSup` / 引理 `ωScottContinuous.iSup`

English:
lemma ωScottContinuous.iSup
  given: {f : ι -> α -> β} (hf : forall i, ωScottContinuous (f i))
  proof: by
  refine ωScottContinuous.of_monotone_map_ωSup
    ⟨Monotone.iSup fun i => (hf i).monotone, fun c => eq_of_forall_ge_iff fun a => ?_⟩
  simp +contextual [ωSup_le_iff, (hf _).map_ωSup, @forall_comm ι]

中文:
引理 ωScottContinuous.iSup
  条件: {f : ι -> α -> β} (hf : 对任意 i, ωScottContinuous (f i))
  证明: by
  refine ωScottContinuous.of_monotone_map_ωSup
    ⟨Monotone.iSup fun i => (hf i).monotone, fun c => eq_of_forall_ge_iff fun a => ?_⟩
  simp +contextual [ωSup_le_iff, (hf _).map_ωSup, @forall_comm ι]

Depends on / 依赖: Monotone, Monotone.iSup, ScottContinuous.of_monotone_map_, contextual, eq_of_forall_ge_iff, forall_comm, monotone
-/
lemma ωScottContinuous.iSup {f : ι -> α -> β} (hf : forall i, ωScottContinuous (f i)) :
    ωScottContinuous (⨆ i, f i) := by
  refine ωScottContinuous.of_monotone_map_ωSup
    ⟨Monotone.iSup fun i => (hf i).monotone, fun c => eq_of_forall_ge_iff fun a => ?_⟩
  simp +contextual [ωSup_le_iff, (hf _).map_ωSup, @forall_comm ι]

/--
lemma `ωScottContinuous.sSup` / 引理 `ωScottContinuous.sSup`

English:
lemma ωScottContinuous.sSup
  given: {s : Set (α -> β)} (hs : forall f in s, ωScottContinuous f)
  proof: by
rw [sSup_eq_iSup]; apply ωScottContinuous.iSup fun f => ωScottContinuous.iSup hs f

中文:
引理 ωScottContinuous.sSup
  条件: {s : Set (α -> β)} (hs : 对任意 f in s, ωScottContinuous f)
  证明: by
rw [sSup_eq_iSup]; apply ωScottContinuous.iSup fun f => ωScottContinuous.iSup hs f

Depends on / 依赖: ScottContinuous.iSup, sSup_eq_iSup
-/
lemma ωScottContinuous.sSup {s : Set (α -> β)} (hs : forall f in s, ωScottContinuous f) :
    ωScottContinuous (sSup s) := by
rw [sSup_eq_iSup]; apply ωScottContinuous.iSup fun f => ωScottContinuous.iSup hs f

/--
lemma `ωScottContinuous.sup` / 引理 `ωScottContinuous.sup`

English:
lemma ωScottContinuous.sup
  given: (hf : ωScottContinuous f) (hg : ωScottContinuous g)
  proof: by
  rw [← sSup_pair]
  apply ωScottContinuous.sSup
  rintro f (rfl | rfl | _) <;> assumption

#adaptation_note

中文:
引理 ωScottContinuous.sup
  条件: (hf : ωScottContinuous f) (hg : ωScottContinuous g)
  证明: by
  rw [← sSup_pair]
  apply ωScottContinuous.sSup
  rintro f (rfl | rfl | _) <;> assumption

#adaptation_note

Depends on / 依赖: ScottContinuous.sSup, sSup_pair
-/
lemma ωScottContinuous.sup (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous (f ⊔ g) := by
  rw [← sSup_pair]
  apply ωScottContinuous.sSup
  rintro f (rfl | rfl | _) <;> assumption

#adaptation_note
/--
Why `respectTransparency.types false` here?
The proof of this lemma involves a very subtle form of abuse of definitional equality.
`monotone_const` is only applicable if `Top.top` (`⊤`) can be unfolded to see that it's constant.
However, `Top.top` is semireducible.
This mismatch is problematic because `simp` works at implicit transparency.
-/
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ωScottContinuous.top` / 引理 `ωScottContinuous.top`

English:
lemma ωScottContinuous.top
  statement: ωScottContinuous (⊤ : α -> β)
  proof: ωScottContinuous.of_monotone_map_ωSup
    ⟨monotone_const, fun c => eq_of_forall_ge_iff fun a => by simp⟩

中文:
引理 ωScottContinuous.top
  结论: ωScottContinuous (⊤ : α -> β)
  证明: ωScottContinuous.of_monotone_map_ωSup
    ⟨monotone_const, fun c => eq_of_forall_ge_iff fun a => by simp⟩

Depends on / 依赖: ScottContinuous.of_monotone_map_, eq_of_forall_ge_iff, monotone_const
-/
lemma ωScottContinuous.top : ωScottContinuous (⊤ : α -> β) :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨monotone_const, fun c => eq_of_forall_ge_iff fun a => by simp⟩

/--
lemma `ωScottContinuous.bot` / 引理 `ωScottContinuous.bot`

English:
lemma ωScottContinuous.bot
  statement: ωScottContinuous (⊥ : α -> β)
  proof: by
  rw [← sSup_empty]; exact ωScottContinuous.sSup (by simp)

中文:
引理 ωScottContinuous.bot
  结论: ωScottContinuous (⊥ : α -> β)
  证明: by
  rw [← sSup_empty]; exact ωScottContinuous.sSup (by simp)

Depends on / 依赖: ScottContinuous.sSup, sSup_empty
-/
lemma ωScottContinuous.bot : ωScottContinuous (⊥ : α -> β) := by
  rw [← sSup_empty]; exact ωScottContinuous.sSup (by simp)

end CompleteLattice

namespace CompleteLattice

variable [OmegaCompletePartialOrder α] [CompleteLinearOrder β] {f g : α -> β}

-- TODO Prove this result for `ScottContinuousOn` and deduce this as a special case
-- Also consider if it holds in greater generality (e.g. finite sets)
-- N.B. The Scott Topology coincides with the Upper Topology on a Complete Linear Order
-- `Topology.IsScott.scott_eq_upper_of_completeLinearOrder`
-- We have that the product topology coincides with the upper topology
-- https://github.com/leanprover-community/mathlib4/pull/12133
/--
lemma `ωScottContinuous.inf` / 引理 `ωScottContinuous.inf`

English:
lemma ωScottContinuous.inf
  given: (hf : ωScottContinuous f) (hg : ωScottContinuous g)
  proof: by
  refine ωScottContinuous.of_monotone_map_ωSup
    ⟨hf.monotone.inf hg.monotone, fun c => eq_of_forall_ge_iff fun a => ?_⟩
  simp only [Pi.inf_apply, hf.map_ωSup c, hg.map_ωSup c, inf_le_iff, ωSup_le_iff, Chain.coe_map,
    Function.comp, OrderHom.coe_mk, ← forall_or_left, ← forall_or_right]
  ex

中文:
引理 ωScottContinuous.inf
  条件: (hf : ωScottContinuous f) (hg : ωScottContinuous g)
  证明: by
  refine ωScottContinuous.of_monotone_map_ωSup
    ⟨hf.monotone.inf hg.monotone, fun c => eq_of_forall_ge_iff fun a => ?_⟩
  simp only [Pi.inf_apply, hf.map_ωSup c, hg.map_ωSup c, inf_le_iff, ωSup_le_iff, Chain.coe_map,
    Function.comp, OrderHom.coe_mk, ← forall_or_left, ← forall_or_right]
  ex

Depends on / 依赖: Chain.coe_map, Function, Function.comp, OrderHom, OrderHom.coe_mk, Pi.inf_apply, ScottContinuous.of_monotone_map_, c.mono, coe_map, coe_mk, eq_of_forall_ge_iff, forall_or_left, forall_or_right, hf.map_, hf.monotone, hf.monotone.inf, hg.map_, hg.monotone, inf_apply, inf_le_iff
-/
lemma ωScottContinuous.inf (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous (f ⊓ g) := by
  refine ωScottContinuous.of_monotone_map_ωSup
    ⟨hf.monotone.inf hg.monotone, fun c => eq_of_forall_ge_iff fun a => ?_⟩
  simp only [Pi.inf_apply, hf.map_ωSup c, hg.map_ωSup c, inf_le_iff, ωSup_le_iff, Chain.coe_map,
    Function.comp, OrderHom.coe_mk, ← forall_or_left, ← forall_or_right]
  exact ⟨fun h _ => h _ _, fun h i j =>
    (h (max j i)).imp (le_trans <| hf.monotone <| c.mono <| le_max_left _ _)
      (le_trans <| hg.monotone <| c.mono <| le_max_right _ _)⟩

end CompleteLattice
