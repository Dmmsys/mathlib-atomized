/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# `Filter.atTop` and `Filter.atBot` in (conditionally) complete lattices
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

@[nontriviality]
/--
theorem `Subsingleton.atTop_eq` / 定理 `Subsingleton.atTop_eq`

English:
theorem Subsingleton.atTop_eq
  given: (α) [Subsingleton α] [Preorder α]
  statement: (atTop : Filter α) = ⊤
  proof: by
  refine top_unique fun s hs x => ?_
  rw [atTop]; rw [ciInf_subsingleton x]; rw [mem_principal] at hs
  exact hs self_mem_Ici

@[nontriviality]

中文:
定理 Subsingleton.atTop_eq
  条件: (α) [Subsingleton α] [Preorder α]
  结论: (atTop : Filter α) = ⊤
  证明: by
  refine top_unique fun s hs x => ?_
  rw [atTop]; rw [ciInf_subsingleton x]; rw [mem_principal] at hs
  exact hs self_mem_Ici

@[nontriviality]

Depends on / 依赖: H.symm_of_commute, ciInf_subsingleton, mem_principal, mul_comm, self_mem_Ici, symm_of_commute, top_unique
-/
theorem Subsingleton.atTop_eq (α) [Subsingleton α] [Preorder α] : (atTop : Filter α) = ⊤ := by
  refine top_unique fun s hs x => ?_
  rw [atTop]; rw [ciInf_subsingleton x]; rw [mem_principal] at hs
  exact hs self_mem_Ici

@[nontriviality]
/--
theorem `Subsingleton.atBot_eq` / 定理 `Subsingleton.atBot_eq`

English:
theorem Subsingleton.atBot_eq
  given: (α) [Subsingleton α] [Preorder α]
  statement: (atBot : Filter α) = ⊤
  proof: @Subsingleton.atTop_eq αᵒᵈ _ _

中文:
定理 Subsingleton.atBot_eq
  条件: (α) [Subsingleton α] [Preorder α]
  结论: (atBot : Filter α) = ⊤
  证明: @Subsingleton.atTop_eq αᵒᵈ _ _

Depends on / 依赖: Subsingleton, Subsingleton.atTop_eq, atTop_eq
-/
theorem Subsingleton.atBot_eq (α) [Subsingleton α] [Preorder α] : (atBot : Filter α) = ⊤ :=
  @Subsingleton.atTop_eq αᵒᵈ _ _

/--
theorem `_root_.Monotone.ciSup_comp_tendsto_atTop` / 定理 `_root_.Monotone.ciSup_comp_tendsto_atTop`

English:
theorem _root_.Monotone.ciSup_comp_tendsto_atTop
  statement: [Preorder β] [ConditionallyCompleteLattice γ]
  proof: by
  have : Nonempty α := nonempty_of_neBot l
  have : Nonempty β := .map g ‹_›
  rw [← csInf_upperBounds_range]; rw [← csInf_upperBounds_range]; rw [← hf.upperBounds_range_comp_tendsto_atTop hg]; rw [Function.comp_def]
  exacts [hb, hb.mono <| range_comp_subset_range _ _]

中文:
定理 _root_.Monotone.ciSup_comp_tendsto_atTop
  结论: [Preorder β] [ConditionallyCompleteLattice γ]
  证明: by
  have : Nonempty α := nonempty_of_neBot l
  have : Nonempty β := .map g ‹_›
  rw [← csInf_upperBounds_range]; rw [← csInf_upperBounds_range]; rw [← hf.upperBounds_range_comp_tendsto_atTop hg]; rw [Function.comp_def]
  exacts [hb, hb.mono <| range_comp_subset_range _ _]

Depends on / 依赖: Function, Function.comp_def, Nonempty, comp_def, csInf_upperBounds_range, exacts, hb.mono, hf.upperBounds_range_comp_tendsto_atTop, nonempty_of_neBot, range_comp_subset_range, upperBounds_range_comp_tendsto_atTop
-/
theorem _root_.Monotone.ciSup_comp_tendsto_atTop [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Monotone f) (hb : BddAbove (range f))
    {g : α -> β} (hg : Tendsto g l atTop) : ⨆ a, f (g a) = ⨆ b, f b := by
  have : Nonempty α := nonempty_of_neBot l
  have : Nonempty β := .map g ‹_›
  rw [← csInf_upperBounds_range]; rw [← csInf_upperBounds_range]; rw [← hf.upperBounds_range_comp_tendsto_atTop hg]; rw [Function.comp_def]
  exacts [hb, hb.mono <| range_comp_subset_range _ _]

/--
theorem `_root_.Monotone.ciInf_comp_tendsto_atBot` / 定理 `_root_.Monotone.ciInf_comp_tendsto_atBot`

English:
theorem _root_.Monotone.ciInf_comp_tendsto_atBot
  statement: [Preorder β] [ConditionallyCompleteLattice γ]
  proof: hf.dual.ciSup_comp_tendsto_atTop hb hg

中文:
定理 _root_.Monotone.ciInf_comp_tendsto_atBot
  结论: [Preorder β] [ConditionallyCompleteLattice γ]
  证明: hf.dual.ciSup_comp_tendsto_atTop hb hg

Depends on / 依赖: ciSup_comp_tendsto_atTop, hf.dual.ciSup_comp_tendsto_atTop
-/
theorem _root_.Monotone.ciInf_comp_tendsto_atBot [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Monotone f) (hb : BddBelow (range f))
    {g : α -> β} (hg : Tendsto g l atBot) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atTop hb hg

/--
theorem `_root_.Antitone.ciSup_comp_tendsto_atBot` / 定理 `_root_.Antitone.ciSup_comp_tendsto_atBot`

English:
theorem _root_.Antitone.ciSup_comp_tendsto_atBot
  statement: [Preorder β] [ConditionallyCompleteLattice γ]
  proof: hf.dual_left.ciSup_comp_tendsto_atTop hb hg

中文:
定理 _root_.Antitone.ciSup_comp_tendsto_atBot
  结论: [Preorder β] [ConditionallyCompleteLattice γ]
  证明: hf.dual_left.ciSup_comp_tendsto_atTop hb hg

Depends on / 依赖: ciSup_comp_tendsto_atTop, dual_left, hf.dual_left.ciSup_comp_tendsto_atTop
-/
theorem _root_.Antitone.ciSup_comp_tendsto_atBot [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Antitone f) (hb : BddAbove (range f))
    {g : α -> β} (hg : Tendsto g l atBot) : ⨆ a, f (g a) = ⨆ b, f b :=
  hf.dual_left.ciSup_comp_tendsto_atTop hb hg

/--
theorem `_root_.Antitone.ciInf_comp_tendsto_atTop` / 定理 `_root_.Antitone.ciInf_comp_tendsto_atTop`

English:
theorem _root_.Antitone.ciInf_comp_tendsto_atTop
  statement: [Preorder β] [ConditionallyCompleteLattice γ]
  proof: hf.dual.ciSup_comp_tendsto_atBot hb hg

中文:
定理 _root_.Antitone.ciInf_comp_tendsto_atTop
  结论: [Preorder β] [ConditionallyCompleteLattice γ]
  证明: hf.dual.ciSup_comp_tendsto_atBot hb hg

Depends on / 依赖: ciSup_comp_tendsto_atBot, hf.dual.ciSup_comp_tendsto_atBot
-/
theorem _root_.Antitone.ciInf_comp_tendsto_atTop [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Antitone f) (hb : BddBelow (range f))
    {g : α -> β} (hg : Tendsto g l atTop) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atBot hb hg

/--
theorem `_root_.Monotone.ciSup_comp_tendsto_atTop_of_linearOrder` / 定理 `_root_.Monotone.ciSup_comp_tendsto_atTop_of_linearOrder`

English:
theorem _root_.Monotone.ciSup_comp_tendsto_atTop_of_linearOrder
  statement: [Preorder β]
  proof: by
  if hb : BddAbove (range f) then
    exact hf.ciSup_comp_tendsto_atTop hb hg
  else
    rw [iSup]; rw [iSup]; rw [csSup_of_not_bddAbove]; rw [csSup_of_not_bddAbove hb]
    rwa [BddAbove, ← Function.comp_def f g, hf.upperBounds_range_comp_tendsto_atTop hg]

中文:
定理 _root_.Monotone.ciSup_comp_tendsto_atTop_of_linearOrder
  结论: [Preorder β]
  证明: by
  if hb : BddAbove (range f) then
    exact hf.ciSup_comp_tendsto_atTop hb hg
  else
    rw [iSup]; rw [iSup]; rw [csSup_of_not_bddAbove]; rw [csSup_of_not_bddAbove hb]
    rwa [BddAbove, ← Function.comp_def f g, hf.upperBounds_range_comp_tendsto_atTop hg]

Depends on / 依赖: BddAbove, Function, Function.comp_def, ciSup_comp_tendsto_atTop, comp_def, csSup_of_not_bddAbove, hf.ciSup_comp_tendsto_atTop, hf.upperBounds_range_comp_tendsto_atTop, upperBounds_range_comp_tendsto_atTop
-/
theorem _root_.Monotone.ciSup_comp_tendsto_atTop_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Monotone f)
    {g : α -> β} (hg : Tendsto g l atTop) : ⨆ a, f (g a) = ⨆ b, f b := by
  if hb : BddAbove (range f) then
    exact hf.ciSup_comp_tendsto_atTop hb hg
  else
    rw [iSup]; rw [iSup]; rw [csSup_of_not_bddAbove]; rw [csSup_of_not_bddAbove hb]
    rwa [BddAbove, ← Function.comp_def f g, hf.upperBounds_range_comp_tendsto_atTop hg]

/--
theorem `_root_.Monotone.ciInf_comp_tendsto_atBot_of_linearOrder` / 定理 `_root_.Monotone.ciInf_comp_tendsto_atBot_of_linearOrder`

English:
theorem _root_.Monotone.ciInf_comp_tendsto_atBot_of_linearOrder
  statement: [Preorder β]
  proof: hf.dual.ciSup_comp_tendsto_atTop_of_linearOrder hg

中文:
定理 _root_.Monotone.ciInf_comp_tendsto_atBot_of_linearOrder
  结论: [Preorder β]
  证明: hf.dual.ciSup_comp_tendsto_atTop_of_linearOrder hg

Depends on / 依赖: ciSup_comp_tendsto_atTop_of_linearOrder, hf.dual.ciSup_comp_tendsto_atTop_of_linearOrder
-/
theorem _root_.Monotone.ciInf_comp_tendsto_atBot_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Monotone f)
    {g : α -> β} (hg : Tendsto g l atBot) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atTop_of_linearOrder hg

/--
theorem `_root_.Antitone.ciInf_comp_tendsto_atTop_of_linearOrder` / 定理 `_root_.Antitone.ciInf_comp_tendsto_atTop_of_linearOrder`

English:
theorem _root_.Antitone.ciInf_comp_tendsto_atTop_of_linearOrder
  statement: [Preorder β]
  proof: hf.dual_left.ciInf_comp_tendsto_atBot_of_linearOrder hg

中文:
定理 _root_.Antitone.ciInf_comp_tendsto_atTop_of_linearOrder
  结论: [Preorder β]
  证明: hf.dual_left.ciInf_comp_tendsto_atBot_of_linearOrder hg

Depends on / 依赖: ciInf_comp_tendsto_atBot_of_linearOrder, dual_left, hf.dual_left.ciInf_comp_tendsto_atBot_of_linearOrder
-/
theorem _root_.Antitone.ciInf_comp_tendsto_atTop_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Antitone f)
    {g : α -> β} (hg : Tendsto g l atTop) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual_left.ciInf_comp_tendsto_atBot_of_linearOrder hg

/--
theorem `_root_.Antitone.ciSup_comp_tendsto_atBot_of_linearOrder` / 定理 `_root_.Antitone.ciSup_comp_tendsto_atBot_of_linearOrder`

English:
theorem _root_.Antitone.ciSup_comp_tendsto_atBot_of_linearOrder
  statement: [Preorder β]
  proof: hf.dual_left.ciSup_comp_tendsto_atTop_of_linearOrder hg

中文:
定理 _root_.Antitone.ciSup_comp_tendsto_atBot_of_linearOrder
  结论: [Preorder β]
  证明: hf.dual_left.ciSup_comp_tendsto_atTop_of_linearOrder hg

Depends on / 依赖: ciSup_comp_tendsto_atTop_of_linearOrder, dual_left, hf.dual_left.ciSup_comp_tendsto_atTop_of_linearOrder
-/
theorem _root_.Antitone.ciSup_comp_tendsto_atBot_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Antitone f)
    {g : α -> β} (hg : Tendsto g l atBot) : ⨆ a, f (g a) = ⨆ b, f b :=
  hf.dual_left.ciSup_comp_tendsto_atTop_of_linearOrder hg

/--
theorem `_root_.Monotone.iSup_comp_tendsto_atTop` / 定理 `_root_.Monotone.iSup_comp_tendsto_atTop`

English:
theorem _root_.Monotone.iSup_comp_tendsto_atTop
  proof: hf.ciSup_comp_tendsto_atTop (OrderTop.bddAbove _) hg

中文:
定理 _root_.Monotone.iSup_comp_tendsto_atTop
  证明: hf.ciSup_comp_tendsto_atTop (OrderTop.bddAbove _) hg

Depends on / 依赖: OrderTop, OrderTop.bddAbove, bddAbove, ciSup_comp_tendsto_atTop, hf.ciSup_comp_tendsto_atTop
-/
theorem _root_.Monotone.iSup_comp_tendsto_atTop
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderTop γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Monotone f) {g : α -> β} (hg : Tendsto g l atTop) :
    ⨆ a, f (g a) = ⨆ b, f b :=
  hf.ciSup_comp_tendsto_atTop (OrderTop.bddAbove _) hg

/--
theorem `_root_.Monotone.iInf_comp_tendsto_atBot` / 定理 `_root_.Monotone.iInf_comp_tendsto_atBot`

English:
theorem _root_.Monotone.iInf_comp_tendsto_atBot
  proof: hf.ciInf_comp_tendsto_atBot (OrderBot.bddBelow _) hg

中文:
定理 _root_.Monotone.iInf_comp_tendsto_atBot
  证明: hf.ciInf_comp_tendsto_atBot (OrderBot.bddBelow _) hg

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, ciInf_comp_tendsto_atBot, hf.ciInf_comp_tendsto_atBot
-/
theorem _root_.Monotone.iInf_comp_tendsto_atBot
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderBot γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Monotone f) {g : α -> β} (hg : Tendsto g l atBot) :
    ⨅ a, f (g a) = ⨅ b, f b :=
  hf.ciInf_comp_tendsto_atBot (OrderBot.bddBelow _) hg

/--
theorem `_root_.Antitone.iSup_comp_tendsto_atBot` / 定理 `_root_.Antitone.iSup_comp_tendsto_atBot`

English:
theorem _root_.Antitone.iSup_comp_tendsto_atBot
  proof: hf.ciSup_comp_tendsto_atBot (OrderTop.bddAbove _) hg

中文:
定理 _root_.Antitone.iSup_comp_tendsto_atBot
  证明: hf.ciSup_comp_tendsto_atBot (OrderTop.bddAbove _) hg

Depends on / 依赖: OrderTop, OrderTop.bddAbove, bddAbove, ciSup_comp_tendsto_atBot, hf.ciSup_comp_tendsto_atBot
-/
theorem _root_.Antitone.iSup_comp_tendsto_atBot
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderTop γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Antitone f) {g : α -> β} (hg : Tendsto g l atBot) :
    ⨆ a, f (g a) = ⨆ b, f b :=
  hf.ciSup_comp_tendsto_atBot (OrderTop.bddAbove _) hg

/--
theorem `_root_.Antitone.iInf_comp_tendsto_atTop` / 定理 `_root_.Antitone.iInf_comp_tendsto_atTop`

English:
theorem _root_.Antitone.iInf_comp_tendsto_atTop
  proof: hf.ciInf_comp_tendsto_atTop (OrderBot.bddBelow _) hg

中文:
定理 _root_.Antitone.iInf_comp_tendsto_atTop
  证明: hf.ciInf_comp_tendsto_atTop (OrderBot.bddBelow _) hg

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, ciInf_comp_tendsto_atTop, hf.ciInf_comp_tendsto_atTop
-/
theorem _root_.Antitone.iInf_comp_tendsto_atTop
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderBot γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Antitone f) {g : α -> β} (hg : Tendsto g l atTop) :
    ⨅ a, f (g a) = ⨅ b, f b :=
  hf.ciInf_comp_tendsto_atTop (OrderBot.bddBelow _) hg

/--
theorem `_root_.Monotone.iUnion_comp_tendsto_atTop` / 定理 `_root_.Monotone.iUnion_comp_tendsto_atTop`

English:
theorem _root_.Monotone.iUnion_comp_tendsto_atTop
  statement: [Preorder β] {l : Filter α} [l.NeBot]
  proof: hs.iSup_comp_tendsto_atTop hf

中文:
定理 _root_.Monotone.iUnion_comp_tendsto_atTop
  结论: [Preorder β] {l : Filter α} [l.NeBot]
  证明: hs.iSup_comp_tendsto_atTop hf

Depends on / 依赖: hs.iSup_comp_tendsto_atTop, iSup_comp_tendsto_atTop
-/
theorem _root_.Monotone.iUnion_comp_tendsto_atTop [Preorder β] {l : Filter α} [l.NeBot]
    {s : β -> Set γ} (hs : Monotone s) {f : α -> β} (hf : Tendsto f l atTop) :
    ⋃ a, s (f a) = ⋃ b, s b :=
  hs.iSup_comp_tendsto_atTop hf

/--
theorem `_root_.Monotone.iInter_comp_tendsto_atBot` / 定理 `_root_.Monotone.iInter_comp_tendsto_atBot`

English:
theorem _root_.Monotone.iInter_comp_tendsto_atBot
  statement: [Preorder β] {l : Filter α} [l.NeBot]
  proof: hs.iInf_comp_tendsto_atBot hf

中文:
定理 _root_.Monotone.iInter_comp_tendsto_atBot
  结论: [Preorder β] {l : Filter α} [l.NeBot]
  证明: hs.iInf_comp_tendsto_atBot hf

Depends on / 依赖: hs.iInf_comp_tendsto_atBot, iInf_comp_tendsto_atBot
-/
theorem _root_.Monotone.iInter_comp_tendsto_atBot [Preorder β] {l : Filter α} [l.NeBot]
    {s : β -> Set γ} (hs : Monotone s) {f : α -> β} (hf : Tendsto f l atBot) :
    ⋂ a, s (f a) = ⋂ b, s b :=
  hs.iInf_comp_tendsto_atBot hf

/--
theorem `_root_.Antitone.iInter_comp_tendsto_atTop` / 定理 `_root_.Antitone.iInter_comp_tendsto_atTop`

English:
theorem _root_.Antitone.iInter_comp_tendsto_atTop
  statement: [Preorder β] {l : Filter α} [l.NeBot]
  proof: hs.iInf_comp_tendsto_atTop hf

中文:
定理 _root_.Antitone.iInter_comp_tendsto_atTop
  结论: [Preorder β] {l : Filter α} [l.NeBot]
  证明: hs.iInf_comp_tendsto_atTop hf

Depends on / 依赖: hs.iInf_comp_tendsto_atTop, iInf_comp_tendsto_atTop
-/
theorem _root_.Antitone.iInter_comp_tendsto_atTop [Preorder β] {l : Filter α} [l.NeBot]
    {s : β -> Set γ} (hs : Antitone s) {f : α -> β} (hf : Tendsto f l atTop) :
    ⋂ a, s (f a) = ⋂ b, s b :=
  hs.iInf_comp_tendsto_atTop hf

/--
theorem `_root_.Antitone.iUnion_comp_tendsto_atBot` / 定理 `_root_.Antitone.iUnion_comp_tendsto_atBot`

English:
theorem _root_.Antitone.iUnion_comp_tendsto_atBot
  statement: [Preorder β] {l : Filter α} [l.NeBot]
  proof: hs.iSup_comp_tendsto_atBot hf

中文:
定理 _root_.Antitone.iUnion_comp_tendsto_atBot
  结论: [Preorder β] {l : Filter α} [l.NeBot]
  证明: hs.iSup_comp_tendsto_atBot hf

Depends on / 依赖: hs.iSup_comp_tendsto_atBot, iSup_comp_tendsto_atBot
-/
theorem _root_.Antitone.iUnion_comp_tendsto_atBot [Preorder β] {l : Filter α} [l.NeBot]
    {s : β -> Set γ} (hs : Antitone s) {f : α -> β} (hf : Tendsto f l atBot) :
    ⋃ a, s (f a) = ⋃ b, s b :=
  hs.iSup_comp_tendsto_atBot hf

end Filter
