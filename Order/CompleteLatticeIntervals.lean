/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.Interval.Set.OrdConnected

/-! # Subtypes of conditionally complete linear orders

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `OrdConnected` set satisfies these conditions.

## TODO

Add appropriate instances for all `Set.Ixx`. This requires a refactor that will allow different
default values for `sSup` and `sInf`.
-/

@[expose] public section

assert_not_exists Multiset

open Set

variable {ι : Sort*} {α : Type*} (s : Set α)

section SupSet

variable [Preorder α] [SupSet α]

open scoped Classical in
/-- `SupSet` structure on a nonempty subset `s` of a preorder with `SupSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
@[instance_reducible]
/--
Definition of `subsetSupSet` / `subsetSupSet` 的定义

English:
definition subsetSupSet
  signature: [Inhabited s]
  body: if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) in s
    then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
    else default

中文:
定义 subsetSupSet
  签名: [Inhabited s]
  定义体: if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) in s
    then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
    else default

Depends on / 依赖: BddAbove, Nonempty, t.Nonempty
-/
noncomputable def subsetSupSet [Inhabited s] : SupSet s where
  sSup t :=
    if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) in s
    then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
    else default

attribute [local instance] subsetSupSet

open scoped Classical in
@[simp]
/--
theorem `subset_sSup_def` / 定理 `subset_sSup_def`

English:
theorem subset_sSup_def
  given: [Inhabited s]
  proof: rfl

中文:
定理 subset_sSup_def
  条件: [Inhabited s]
  证明: rfl
-/
theorem subset_sSup_def [Inhabited s] :
    @sSup s _ = fun t =>
      if ht : t.Nonempty ∧ BddAbove t ∧ sSup ((↑) '' t : Set α) in s
      then ⟨sSup ((↑) '' t : Set α), ht.2.2⟩
      else default :=
  rfl

/--
theorem `subset_sSup_of_within` / 定理 `subset_sSup_of_within`

English:
theorem subset_sSup_of_within
  statement: [Inhabited s] {t : Set s}
  proof: by simp [h, h', h'']

中文:
定理 subset_sSup_of_within
  结论: [Inhabited s] {t : Set s}
  证明: by simp [h, h', h'']
-/
theorem subset_sSup_of_within [Inhabited s] {t : Set s}
    (h' : t.Nonempty) (h'' : BddAbove t) (h : sSup ((↑) '' t : Set α) in s) :
    sSup ((↑) '' t : Set α) = (@sSup s _ t : α) := by simp [h, h', h'']

/--
theorem `subset_sSup_emptyset` / 定理 `subset_sSup_emptyset`

English:
theorem subset_sSup_emptyset
  given: [Inhabited s]
  proof: by
  simp [sSup]

中文:
定理 subset_sSup_emptyset
  条件: [Inhabited s]
  证明: by
  simp [sSup]
-/
theorem subset_sSup_emptyset [Inhabited s] :
    sSup (∅ : Set s) = default := by
  simp [sSup]

/--
theorem `subset_sSup_of_not_bddAbove` / 定理 `subset_sSup_of_not_bddAbove`

English:
theorem subset_sSup_of_not_bddAbove
  given: [Inhabited s] {t : Set s} (ht : ¬BddAbove t)
  proof: by
  simp [sSup, ht]

中文:
定理 subset_sSup_of_not_bddAbove
  条件: [Inhabited s] {t : Set s} (ht : ¬BddAbove t)
  证明: by
  simp [sSup, ht]
-/
theorem subset_sSup_of_not_bddAbove [Inhabited s] {t : Set s} (ht : ¬BddAbove t) :
    sSup t = default := by
  simp [sSup, ht]

end SupSet

section InfSet

variable [Preorder α] [InfSet α]

open scoped Classical in
/-- `InfSet` structure on a nonempty subset `s` of a preorder with `InfSet`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `ConditionallyCompleteLinearOrder` structure. -/
@[instance_reducible]
/--
Definition of `subsetInfSet` / `subsetInfSet` 的定义

English:
definition subsetInfSet
  signature: [Inhabited s]
  body: if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) in s
    then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩
    else default

中文:
定义 subsetInfSet
  签名: [Inhabited s]
  定义体: if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) in s
    then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩
    else default

Depends on / 依赖: BddBelow, Nonempty, t.Nonempty
-/
noncomputable def subsetInfSet [Inhabited s] : InfSet s where
  sInf t :=
    if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) in s
    then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩
    else default

attribute [local instance] subsetInfSet

open scoped Classical in
@[simp]
/--
theorem `subset_sInf_def` / 定理 `subset_sInf_def`

English:
theorem subset_sInf_def
  given: [Inhabited s]
  proof: rfl

中文:
定理 subset_sInf_def
  条件: [Inhabited s]
  证明: rfl
-/
theorem subset_sInf_def [Inhabited s] :
    @sInf s _ = fun t =>
      if ht : t.Nonempty ∧ BddBelow t ∧ sInf ((↑) '' t : Set α) in s
      then ⟨sInf ((↑) '' t : Set α), ht.2.2⟩ else
      default :=
  rfl

/--
theorem `subset_sInf_of_within` / 定理 `subset_sInf_of_within`

English:
theorem subset_sInf_of_within
  statement: [Inhabited s] {t : Set s}
  proof: by simp [h, h', h'']

中文:
定理 subset_sInf_of_within
  结论: [Inhabited s] {t : Set s}
  证明: by simp [h, h', h'']
-/
theorem subset_sInf_of_within [Inhabited s] {t : Set s}
    (h' : t.Nonempty) (h'' : BddBelow t) (h : sInf ((↑) '' t : Set α) in s) :
    sInf ((↑) '' t : Set α) = (@sInf s _ t : α) := by simp [h, h', h'']

/--
theorem `subset_sInf_emptyset` / 定理 `subset_sInf_emptyset`

English:
theorem subset_sInf_emptyset
  given: [Inhabited s]
  proof: by
  simp [sInf]

中文:
定理 subset_sInf_emptyset
  条件: [Inhabited s]
  证明: by
  simp [sInf]
-/
theorem subset_sInf_emptyset [Inhabited s] :
    sInf (∅ : Set s) = default := by
  simp [sInf]

/--
theorem `subset_sInf_of_not_bddBelow` / 定理 `subset_sInf_of_not_bddBelow`

English:
theorem subset_sInf_of_not_bddBelow
  given: [Inhabited s] {t : Set s} (ht : ¬BddBelow t)
  proof: by
  simp [sInf, ht]

中文:
定理 subset_sInf_of_not_bddBelow
  条件: [Inhabited s] {t : Set s} (ht : ¬BddBelow t)
  证明: by
  simp [sInf, ht]
-/
theorem subset_sInf_of_not_bddBelow [Inhabited s] {t : Set s} (ht : ¬BddBelow t) :
    sInf t = default := by
  simp [sInf, ht]

end InfSet

section OrdConnected

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetSupSet

attribute [local instance] subsetInfSet

/--
Definition of `subsetConditionallyCompleteLinearOrder` / `subsetConditionallyCompleteLinearOrder` 的定义

English:
abbreviation subsetConditionallyCompleteLinearOrder
  signature: [Inhabited s]
  body: { subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
isLUB_csSup t ht h_bdd := .of_image Subtype.coe_le_coe by
      rw [← subset_sSup_of_within s ht h_bdd (h_Sup ht h_bdd)]
      exact isLUB_csSup (ht.image _) ((Subtype.mono_coe _).map_bddAbove h_bdd)
isG

中文:
缩写 subsetConditionallyCompleteLinearOrder
  签名: [Inhabited s]
  定义体: { subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
isLUB_csSup t ht h_bdd := .of_image Subtype.coe_le_coe by
      rw [← subset_sSup_of_within s ht h_bdd (h_Sup ht h_bdd)]
      exact isLUB_csSup (ht.image _) ((Subtype.mono_coe _).map_bddAbove h_bdd)
isG

Depends on / 依赖: DistribLattice, DistribLattice.toLattice, LinearOrder, Subtype, Subtype.coe_le_coe, Subtype.mono_coe, coe_le_coe, csSup_of_not_bddAbove, h_Inf, h_Sup, h_bdd, ht.image, isGLB_csInf, isLUB_csSup, map_bddAbove, map_bddBelow, mono_coe, of_image, subsetInfSet, subsetSupSet
-/
noncomputable abbrev subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : forall {t : Set s} (_ : t.Nonempty) (_h_bdd : BddAbove t), sSup ((↑) '' t : Set α) in s)
    (h_Inf : forall {t : Set s} (_ : t.Nonempty) (_h_bdd : BddBelow t), sInf ((↑) '' t : Set α) in s) :
    ConditionallyCompleteLinearOrder s :=
  { subsetSupSet s, subsetInfSet s, DistribLattice.toLattice, (inferInstance : LinearOrder s) with
isLUB_csSup t ht h_bdd := .of_image Subtype.coe_le_coe by
      rw [← subset_sSup_of_within s ht h_bdd (h_Sup ht h_bdd)]
      exact isLUB_csSup (ht.image _) ((Subtype.mono_coe _).map_bddAbove h_bdd)
isGLB_csInf t ht h_bdd := .of_image Subtype.coe_le_coe by
      rw [← subset_sInf_of_within s ht h_bdd (h_Inf ht h_bdd)]
      exact isGLB_csInf (ht.image _) ((Subtype.mono_coe _).map_bddBelow h_bdd)
    csSup_of_not_bddAbove := fun t ht => by simp [ht]
    csInf_of_not_bddBelow := fun t ht => by simp [ht] }

/--
theorem `sSup_within_of_ordConnected` / 定理 `sSup_within_of_ordConnected`

English:
theorem sSup_within_of_ordConnected
  given: {s : Set α} [hs : OrdConnected s] ⦃t
  statement: Set s⦄ (ht : t.Nonempty)
  proof: by
  obtain ⟨c, hct⟩ : exists c, c in t := ht
  obtain ⟨B, hB⟩ : exists B, B in upperBounds t := h_bdd
  refine hs.out c.2 B.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· in s)).le_csSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe (· in s)).csSup_image_le ⟨c, hct⟩ hB

中文:
定理 sSup_within_of_ordConnected
  条件: {s : Set α} [hs : OrdConnected s] ⦃t
  结论: Set s⦄ (ht : t.Nonempty)
  证明: by
  obtain ⟨c, hct⟩ : exists c, c in t := ht
  obtain ⟨B, hB⟩ : exists B, B in upperBounds t := h_bdd
  refine hs.out c.2 B.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· in s)).le_csSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe (· in s)).csSup_image_le ⟨c, hct⟩ hB

Depends on / 依赖: Subtype, Subtype.mono_coe, csSup_image_le, h_bdd, hs.out, le_csSup_image, mono_coe, upperBounds
-/
theorem sSup_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : sSup ((↑) '' t : Set α) in s := by
  obtain ⟨c, hct⟩ : exists c, c in t := ht
  obtain ⟨B, hB⟩ : exists B, B in upperBounds t := h_bdd
  refine hs.out c.2 B.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· in s)).le_csSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe (· in s)).csSup_image_le ⟨c, hct⟩ hB

/--
theorem `sInf_within_of_ordConnected` / 定理 `sInf_within_of_ordConnected`

English:
theorem sInf_within_of_ordConnected
  given: {s : Set α} [hs : OrdConnected s] ⦃t
  statement: Set s⦄ (ht : t.Nonempty)
  proof: by
  obtain ⟨c, hct⟩ : exists c, c in t := ht
  obtain ⟨B, hB⟩ : exists B, B in lowerBounds t := h_bdd
  refine hs.out B.2 c.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· in s)).le_csInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe (· in s)).csInf_image_le hct ⟨B, hB⟩

中文:
定理 sInf_within_of_ordConnected
  条件: {s : Set α} [hs : OrdConnected s] ⦃t
  结论: Set s⦄ (ht : t.Nonempty)
  证明: by
  obtain ⟨c, hct⟩ : exists c, c in t := ht
  obtain ⟨B, hB⟩ : exists B, B in lowerBounds t := h_bdd
  refine hs.out B.2 c.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· in s)).le_csInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe (· in s)).csInf_image_le hct ⟨B, hB⟩

Depends on / 依赖: Subtype, Subtype.mono_coe, csInf_image_le, h_bdd, hs.out, le_csInf_image, lowerBounds, mono_coe
-/
theorem sInf_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : sInf ((↑) '' t : Set α) in s := by
  obtain ⟨c, hct⟩ : exists c, c in t := ht
  obtain ⟨B, hB⟩ : exists B, B in lowerBounds t := h_bdd
  refine hs.out B.2 c.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· in s)).le_csInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe (· in s)).csInf_image_le hct ⟨B, hB⟩

/--
Instance `ordConnectedSubsetConditionallyCompleteLinearOrder` / 实例 `ordConnectedSubsetConditionallyCompleteLinearOrder`

English:
instance ordConnectedSubsetConditionallyCompleteLinearOrder
  signature: [Inhabited s]
  body: subsetConditionallyCompleteLinearOrder s
    (fun h => sSup_within_of_ordConnected h)
    (fun h => sInf_within_of_ordConnected h)

中文:
实例 ordConnectedSubsetConditionallyCompleteLinearOrder
  签名: [Inhabited s]
  定义体: subsetConditionallyCompleteLinearOrder s
    (fun h => sSup_within_of_ordConnected h)
    (fun h => sInf_within_of_ordConnected h)

Depends on / 依赖: sInf_within_of_ordConnected, sSup_within_of_ordConnected, subsetConditionallyCompleteLinearOrder
-/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s]
    [OrdConnected s] : ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s
    (fun h => sSup_within_of_ordConnected h)
    (fun h => sInf_within_of_ordConnected h)

end OrdConnected

section Icc

/--
Instance `Set.Icc.completeLattice` / 实例 `Set.Icc.completeLattice`

English:
instance Set.Icc.completeLattice
  signature: [ConditionallyCompleteLattice α]
  body: (inferInstance : BoundedOrder ↑(Icc a b))
  sSup S := if hS : S = ∅ then ⟨a, le_rfl, Fact.out⟩ else ⟨sSup ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty]; rw [not_not] at hS
    refine ⟨?_, csSup_le (hS.image Subtype.val) (fun _ ⟨c, _, hc⟩ => hc ▸ c.2.2)⟩
    obtain ⟨c, hc⟩ := hS
    exact c

中文:
实例 Set.Icc.completeLattice
  签名: [ConditionallyCompleteLattice α]
  定义体: (inferInstance : BoundedOrder ↑(Icc a b))
  sSup S := if hS : S = ∅ then ⟨a, le_rfl, Fact.out⟩ else ⟨sSup ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty]; rw [not_not] at hS
    refine ⟨?_, csSup_le (hS.image Subtype.val) (fun _ ⟨c, _, hc⟩ => hc ▸ c.2.2)⟩
    obtain ⟨c, hc⟩ := hS
    exact c

Depends on / 依赖: BoundedOrder
-/
noncomputable instance Set.Icc.completeLattice [ConditionallyCompleteLattice α]
    {a b : α} [Fact (a <= b)] : CompleteLattice (Set.Icc a b) where
  __ := (inferInstance : BoundedOrder ↑(Icc a b))
  sSup S := if hS : S = ∅ then ⟨a, le_rfl, Fact.out⟩ else ⟨sSup ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty]; rw [not_not] at hS
    refine ⟨?_, csSup_le (hS.image Subtype.val) (fun _ ⟨c, _, hc⟩ => hc ▸ c.2.2)⟩
    obtain ⟨c, hc⟩ := hS
    exact c.2.1.trans (le_csSup ⟨b, fun _ ⟨d, _, hd⟩ => hd ▸ d.2.2⟩ ⟨c, hc, rfl⟩)⟩
  isLUB_sSup S := by
    split_ifs with hS
    · subst hS; simp only [isLUB_empty_iff, isBot_iff_eq_bot]; rfl
· exact .of_image Subtype.coe_le_coe isLUB_csSup ((Set.nonempty_iff_ne_empty.mpr hS).image _)
        ((Subtype.mono_coe _).map_bddAbove (OrderTop.bddAbove S))
  sInf S := if hS : S = ∅ then ⟨b, Fact.out, le_rfl⟩ else ⟨sInf ((↑) '' S), by
    rw [← Set.not_nonempty_iff_eq_empty]; rw [not_not] at hS
    refine ⟨le_csInf (hS.image Subtype.val) (fun _ ⟨c, _, hc⟩ => hc ▸ c.2.1), ?_⟩
    obtain ⟨c, hc⟩ := hS
    exact le_trans (csInf_le ⟨a, fun _ ⟨d, _, hd⟩ => hd ▸ d.2.1⟩ ⟨c, hc, rfl⟩) c.2.2⟩
  isGLB_sInf S := by
    split_ifs with hS
    · subst hS; simp only [isGLB_empty_iff, isTop_iff_eq_top]; rfl
· exact .of_image Subtype.coe_le_coe isGLB_csInf ((Set.nonempty_iff_ne_empty.mpr hS).image _)
        ((Subtype.mono_coe _).map_bddBelow (OrderBot.bddBelow S))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ConditionallyCompleteLinearOrder
  signature: α] {a b
  body: { Set.Icc.completeLattice, Subtype.instLinearOrder _, LinearOrder.toBiheytingAlgebra _ with }

中文:
实例 [ConditionallyCompleteLinearOrder
  签名: α] {a b
  定义体: { Set.Icc.completeLattice, Subtype.instLinearOrder _, LinearOrder.toBiheytingAlgebra _ with }

Depends on / 依赖: LinearOrder, LinearOrder.toBiheytingAlgebra, Set.Icc.completeLattice, Subtype, Subtype.instLinearOrder, completeLattice, instLinearOrder, toBiheytingAlgebra
-/
noncomputable instance [ConditionallyCompleteLinearOrder α] {a b : α} [Fact (a <= b)] :
    CompleteLinearOrder (Set.Icc a b) :=
  { Set.Icc.completeLattice, Subtype.instLinearOrder _, LinearOrder.toBiheytingAlgebra _ with }

/--
lemma `Set.Icc.coe_sSup` / 引理 `Set.Icc.coe_sSup`

English:
lemma Set.Icc.coe_sSup
  statement: [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
  proof: ⟨h⟩
    ↑(sSup S) = sSup ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)

中文:
引理 Set.Icc.coe_sSup
  结论: [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
  证明: ⟨h⟩
    ↑(sSup S) = sSup ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)
-/
lemma Set.Icc.coe_sSup [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a <= b) := ⟨h⟩
    ↑(sSup S) = sSup ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)

/--
lemma `Set.Icc.coe_sInf` / 引理 `Set.Icc.coe_sInf`

English:
lemma Set.Icc.coe_sInf
  statement: [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
  proof: ⟨h⟩
    ↑(sInf S) = sInf ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)

中文:
引理 Set.Icc.coe_sInf
  结论: [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
  证明: ⟨h⟩
    ↑(sInf S) = sInf ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)
-/
lemma Set.Icc.coe_sInf [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a <= b) := ⟨h⟩
    ↑(sInf S) = sInf ((↑) '' S : Set α) :=
  congrArg Subtype.val (dif_neg hS.ne_empty)

/--
lemma `Set.Icc.coe_iSup` / 引理 `Set.Icc.coe_iSup`

English:
lemma Set.Icc.coe_iSup
  statement: [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
  proof: ⟨h⟩
    ↑(iSup S) = (⨆ i, S i : α) :=
  (Set.Icc.coe_sSup h (range_nonempty S)).trans (congrArg sSup (range_comp Subtype.val S).symm)

中文:
引理 Set.Icc.coe_iSup
  结论: [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
  证明: ⟨h⟩
    ↑(iSup S) = (⨆ i, S i : α) :=
  (Set.Icc.coe_sSup h (range_nonempty S)).trans (congrArg sSup (range_comp Subtype.val S).symm)
-/
lemma Set.Icc.coe_iSup [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
    [Nonempty ι] {S : ι -> Set.Icc a b} : have : Fact (a <= b) := ⟨h⟩
    ↑(iSup S) = (⨆ i, S i : α) :=
  (Set.Icc.coe_sSup h (range_nonempty S)).trans (congrArg sSup (range_comp Subtype.val S).symm)

/--
lemma `Set.Icc.coe_iInf` / 引理 `Set.Icc.coe_iInf`

English:
lemma Set.Icc.coe_iInf
  statement: [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
  proof: ⟨h⟩
    ↑(iInf S) = (⨅ i, S i : α) :=
  (Set.Icc.coe_sInf h (range_nonempty S)).trans (congrArg sInf (range_comp Subtype.val S).symm)

中文:
引理 Set.Icc.coe_iInf
  结论: [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
  证明: ⟨h⟩
    ↑(iInf S) = (⨅ i, S i : α) :=
  (Set.Icc.coe_sInf h (range_nonempty S)).trans (congrArg sInf (range_comp Subtype.val S).symm)
-/
lemma Set.Icc.coe_iInf [ConditionallyCompleteLattice α] {a b : α} (h : a <= b)
    [Nonempty ι] {S : ι -> Set.Icc a b} : have : Fact (a <= b) := ⟨h⟩
    ↑(iInf S) = (⨅ i, S i : α) :=
  (Set.Icc.coe_sInf h (range_nonempty S)).trans (congrArg sInf (range_comp Subtype.val S).symm)

end Icc

namespace Set.Iic

variable [CompleteLattice α] {a : α}

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: : CompleteLattice (Iic a) where
  body: ⟨sSup ((↑) '' S), by simpa using fun b hb _ => hb⟩
  sInf S := ⟨a ⊓ sInf ((↑) '' S), by simp⟩
  isLUB_sSup _ := .of_image Subtype.coe_le_coe (isLUB_sSup _)
  isGLB_sInf _ :=
⟨fun _ hb => inf_le_of_right_le sInf_le mem_image_of_mem Subtype.val hb,
      fun b hb => le_inf_iff.mpr ⟨b.property, le_sInf

中文:
实例 instCompleteLattice
  签名: : CompleteLattice (Iic a) where
  定义体: ⟨sSup ((↑) '' S), by simpa using fun b hb _ => hb⟩
  sInf S := ⟨a ⊓ sInf ((↑) '' S), by simp⟩
  isLUB_sSup _ := .of_image Subtype.coe_le_coe (isLUB_sSup _)
  isGLB_sInf _ :=
⟨fun _ hb => inf_le_of_right_le sInf_le mem_image_of_mem Subtype.val hb,
      fun b hb => le_inf_iff.mpr ⟨b.property, le_sInf
-/
instance instCompleteLattice : CompleteLattice (Iic a) where
  sSup S := ⟨sSup ((↑) '' S), by simpa using fun b hb _ => hb⟩
  sInf S := ⟨a ⊓ sInf ((↑) '' S), by simp⟩
  isLUB_sSup _ := .of_image Subtype.coe_le_coe (isLUB_sSup _)
  isGLB_sInf _ :=
⟨fun _ hb => inf_le_of_right_le sInf_le mem_image_of_mem Subtype.val hb,
      fun b hb => le_inf_iff.mpr ⟨b.property, le_sInf fun _ ⟨_, hd, hd'⟩ => hd' ▸ hb hd⟩⟩
  le_top := by simp
  bot_le := by simp

variable (S : Set <| Iic a) (f : ι -> Iic a) (p : ι -> Prop)

/--
theorem `coe_sSup` / 定理 `coe_sSup`

English:
theorem coe_sSup
  statement: (↑(sSup S) : α) = sSup ((↑) '' S)
  proof: rfl

中文:
定理 coe_sSup
  结论: (↑(sSup S) : α) = sSup ((↑) '' S)
  证明: rfl
-/
@[simp] theorem coe_sSup : (↑(sSup S) : α) = sSup ((↑) '' S) := rfl

/--
theorem `coe_iSup` / 定理 `coe_iSup`

English:
theorem coe_iSup
  statement: (↑(⨆ i, f i) : α) = ⨆ i, (f i : α)
  proof: by
  rw [iSup]; rw [coe_sSup]; congr; ext; simp

中文:
定理 coe_iSup
  结论: (↑(⨆ i, f i) : α) = ⨆ i, (f i : α)
  证明: by
  rw [iSup]; rw [coe_sSup]; congr; ext; simp
-/
@[simp] theorem coe_iSup : (↑(⨆ i, f i) : α) = ⨆ i, (f i : α) := by
  rw [iSup]; rw [coe_sSup]; congr; ext; simp

/--
theorem `coe_biSup` / 定理 `coe_biSup`

English:
theorem coe_biSup
  statement: (↑(⨆ i, ⨆ (_ : p i), f i) : α) = ⨆ i, ⨆ (_ : p i), (f i : α)
  proof: by simp

中文:
定理 coe_biSup
  结论: (↑(⨆ i, ⨆ (_ : p i), f i) : α) = ⨆ i, ⨆ (_ : p i), (f i : α)
  证明: by simp
-/
theorem coe_biSup : (↑(⨆ i, ⨆ (_ : p i), f i) : α) = ⨆ i, ⨆ (_ : p i), (f i : α) := by simp

/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  statement: (↑(sInf S) : α) = a ⊓ sInf ((↑) '' S)
  proof: rfl

中文:
定理 coe_sInf
  结论: (↑(sInf S) : α) = a ⊓ sInf ((↑) '' S)
  证明: rfl
-/
@[simp] theorem coe_sInf : (↑(sInf S) : α) = a ⊓ sInf ((↑) '' S) := rfl

/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  statement: (↑(⨅ i, f i) : α) = a ⊓ ⨅ i, (f i : α)
  proof: by
  rw [iInf]; rw [coe_sInf]; congr; ext; simp

中文:
定理 coe_iInf
  结论: (↑(⨅ i, f i) : α) = a ⊓ ⨅ i, (f i : α)
  证明: by
  rw [iInf]; rw [coe_sInf]; congr; ext; simp
-/
@[simp] theorem coe_iInf : (↑(⨅ i, f i) : α) = a ⊓ ⨅ i, (f i : α) := by
  rw [iInf]; rw [coe_sInf]; congr; ext; simp

/--
theorem `coe_biInf` / 定理 `coe_biInf`

English:
theorem coe_biInf
  statement: (↑(⨅ i, ⨅ (_ : p i), f i) : α) = a ⊓ ⨅ i, ⨅ (_ : p i), (f i : α)
  proof: by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [coe_iInf, ← inf_iInf, ← inf_assoc, inf_idem]

中文:
定理 coe_biInf
  结论: (↑(⨅ i, ⨅ (_ : p i), f i) : α) = a ⊓ ⨅ i, ⨅ (_ : p i), (f i : α)
  证明: by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [coe_iInf, ← inf_iInf, ← inf_assoc, inf_idem]

Depends on / 依赖: coe_iInf, inf_assoc, inf_iInf, inf_idem, isEmpty_or_nonempty, simp_rw
-/
theorem coe_biInf : (↑(⨅ i, ⨅ (_ : p i), f i) : α) = a ⊓ ⨅ i, ⨅ (_ : p i), (f i : α) := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [coe_iInf, ← inf_iInf, ← inf_assoc, inf_idem]


end Set.Iic
