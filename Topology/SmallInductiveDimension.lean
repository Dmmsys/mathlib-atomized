/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu, Andrew Yang
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Clopen

/-!
# Small inductive dimension

The small inductive dimension of a space is inductively defined as follows. Empty spaces have
small inductive dimension less than 0, and a topological space has dimension less than `n + 1` if
it has a topological basis whose elements have frontiers of dimension strictly less `n`.

In this file we formalize this notion, and characterize the cases `n = 0` and `n = 1`.

## Main definitions

* `HasSmallInductiveDimensionLT X n` : Provides a class stating that `X` has small inductive
  dimension less than `n`.
* `HasSmallInductiveDimensionLE X n` : Provides an abbrev for
  `HasSmallInductiveDimensionLT X (n + 1)`.
* `smallInductiveDimension X` : The small inductive dimension of `X`, with values in `WithBot ℕ∞`.

## References

* https://en.wikipedia.org/wiki/Inductive_dimension
-/

@[expose] public section

open Set Topology TopologicalSpace

/--
Definition of `inductive` / `inductive` 的定义

English:
class inductive
  parameters: HasSmallInductiveDimensionLT.{u}
  axioms and operations (2):
    - |(zero {X : Type u} [TopologicalSpace X] [IsEmpty X]) : HasSmallInductiveDimensionLT X 0
    - |(succ {X : Type u} [TopologicalSpace X] (n : Nat) (s : Set (Set X)) (hs : IsTopologicalBasis s) (h : forall U in s, HasSmallInductiveDimensionLT (frontier U) n)) : HasSmallInductiveDimensionLT X (n + 1)

中文:
类 inductive
  参数: HasSmallInductiveDimensionLT.{u}
  公理与运算 (2 个):
    - |(zero {X : 类型u} [拓扑空间 X] [是空 X]) : HasSmallInductiveDimensionLT X 0
    - |(succ {X : 类型u} [拓扑空间 X] (n : 自然数) (s : 集合 (集合 X)) (hs : 是TopologicalBasis s) (h : 对任意 U in s, HasSmallInductiveDimensionLT (frontier U) n)) : HasSmallInductiveDimensionLT X (n + 1)
-/
class inductive HasSmallInductiveDimensionLT.{u} :
  forall (X : Type u) [TopologicalSpace X], Nat -> Prop where
  | zero {X : Type u} [TopologicalSpace X] [IsEmpty X] : HasSmallInductiveDimensionLT X 0
  | succ {X : Type u} [TopologicalSpace X] (n : Nat) (s : Set (Set X)) (hs : IsTopologicalBasis s)
      (h : forall U in s, HasSmallInductiveDimensionLT (frontier U) n) :
      HasSmallInductiveDimensionLT X (n + 1)

variable {X : Type*} [TopologicalSpace X]

variable (X) in
/--
Definition of `HasSmallInductiveDimensionLE` / `HasSmallInductiveDimensionLE` 的定义

English:
abbreviation HasSmallInductiveDimensionLE
  signature: (n : Nat)
  body: HasSmallInductiveDimensionLT X (n + 1)

@[simp]

中文:
缩写 HasSmallInductiveDimensionLE
  签名: (n : 自然数)
  定义体: HasSmallInductiveDimensionLT X (n + 1)

@[simp]

Depends on / 依赖: HasSmallInductiveDimensionLT
-/
abbrev HasSmallInductiveDimensionLE (n : Nat) :=
  HasSmallInductiveDimensionLT X (n + 1)

@[simp]
/--
theorem `hasSmallInductiveDimensionLT_zero_iff` / 定理 `hasSmallInductiveDimensionLT_zero_iff`

English:
theorem hasSmallInductiveDimensionLT_zero_iff
  statement: HasSmallInductiveDimensionLT X 0 ↔ IsEmpty X
  proof: ⟨fun h => by cases h; assumption, fun _ => .zero⟩

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_zero_iff := hasSmallInductiveDimensionLT_zero_iff

中文:
定理 hasSmallInductiveDimensionLT_zero_iff
  结论: HasSmallInductiveDimensionLT X 0 ↔ 是空 X
  证明: ⟨fun h => by cases h; assumption, fun _ => .zero⟩

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_zero_iff := hasSmallInductiveDimensionLT_zero_iff
-/
theorem hasSmallInductiveDimensionLT_zero_iff : HasSmallInductiveDimensionLT X 0 ↔ IsEmpty X :=
  ⟨fun h => by cases h; assumption, fun _ => .zero⟩

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_zero_iff := hasSmallInductiveDimensionLT_zero_iff

/--
lemma `hasSmallInductiveDimensionLT_one_iff` / 引理 `hasSmallInductiveDimensionLT_one_iff`

English:
lemma hasSmallInductiveDimensionLT_one_iff
  proof: by
  constructor
  · intro (.succ _ s hs h)
    refine hs.of_isOpen_of_subset (fun _ hU => hU.isOpen) (fun U hU => ⟨?_, hs.isOpen hU⟩)
    rw [← closure_subset_iff_isClosed]
    cases h U hU
    rwa [isEmpty_coe_sort, (hs.isOpen hU).frontier_eq, sdiff_eq_empty] at ‹_›
  · exact fun h => .succ 0 _ h fun _ hU => hU.frontier_eq ▸ .zero

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_one_iff := hasSmallInductiveDimensionLT_one_iff

中文:
引理 hasSmallInductiveDimensionLT_one_iff
  证明: by
  constructor
  · intro (.succ _ s hs h)
    refine hs.of_isOpen_of_subset (fun _ hU => hU.isOpen) (fun U hU => ⟨?_, hs.isOpen hU⟩)
    rw [← closure_subset_iff_isClosed]
    cases h U hU
    rwa [isEmpty_coe_sort, (hs.isOpen hU).frontier_eq, sdiff_eq_empty] at ‹_›
  · exact fun h => .succ 0 _ h fun _ hU => hU.frontier_eq ▸ .zero

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_one_iff := hasSmallInductiveDimensionLT_one_iff

Depends on / 依赖: closure_subset_iff_isClosed, frontier_eq, hU.frontier_eq, hU.isOpen, hs.isOpen, hs.of_isOpen_of_subset, isEmpty_coe_sort, isOpen, of_isOpen_of_subset, sdiff_eq_empty
-/
lemma hasSmallInductiveDimensionLT_one_iff :
    HasSmallInductiveDimensionLT X 1 ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  constructor
  · intro (.succ _ s hs h)
    refine hs.of_isOpen_of_subset (fun _ hU => hU.isOpen) (fun U hU => ⟨?_, hs.isOpen hU⟩)
    rw [← closure_subset_iff_isClosed]
    cases h U hU
    rwa [isEmpty_coe_sort, (hs.isOpen hU).frontier_eq, sdiff_eq_empty] at ‹_›
  · exact fun h => .succ 0 _ h fun _ hU => hU.frontier_eq ▸ .zero

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_one_iff := hasSmallInductiveDimensionLT_one_iff

/--
theorem `HasSmallInductiveDimensionLT.mono` / 定理 `HasSmallInductiveDimensionLT.mono`

English:
theorem HasSmallInductiveDimensionLT.mono
  statement: {m n : Nat} (hmn : m <= n)
  proof: by
  induction n generalizing m X with
  | zero => simp_all
  | succ m IH =>
    cases H with
    | zero => exact .succ _ ∅ (by simpa) (by simp)
    | succ n s hs h =>
      refine .succ _ s hs fun U hU => IH ?_ (h U hU)
      rwa [add_le_add_iff_right] at hmn

中文:
定理 HasSmallInductiveDimensionLT.mono
  结论: {m n : 自然数} (hmn : m <= n)
  证明: by
  induction n generalizing m X with
  | zero => simp_all
  | succ m IH =>
    cases H with
    | zero => exact .succ _ ∅ (by simpa) (by simp)
    | succ n s hs h =>
      refine .succ _ s hs fun U hU => IH ?_ (h U hU)
      rwa [add_le_add_iff_right] at hmn

Depends on / 依赖: add_le_add_iff_right, generalizing
-/
theorem HasSmallInductiveDimensionLT.mono {m n : Nat} (hmn : m <= n)
    (H : HasSmallInductiveDimensionLT X m) : HasSmallInductiveDimensionLT X n := by
  induction n generalizing m X with
  | zero => simp_all
  | succ m IH =>
    cases H with
    | zero => exact .succ _ ∅ (by simpa) (by simp)
    | succ n s hs h =>
      refine .succ _ s hs fun U hU => IH ?_ (h U hU)
      rwa [add_le_add_iff_right] at hmn

/--
theorem `HasSmallInductiveDimensionLE.mono` / 定理 `HasSmallInductiveDimensionLE.mono`

English:
theorem HasSmallInductiveDimensionLE.mono
  statement: {m n : Nat} (hmn : m <= n)
  proof: by
  apply HasSmallInductiveDimensionLT.mono _ H
  rwa [add_le_add_iff_right]

中文:
定理 HasSmallInductiveDimensionLE.mono
  结论: {m n : 自然数} (hmn : m <= n)
  证明: by
  apply HasSmallInductiveDimensionLT.mono _ H
  rwa [add_le_add_iff_right]

Depends on / 依赖: HasSmallInductiveDimensionLT, HasSmallInductiveDimensionLT.mono, add_le_add_iff_right
-/
theorem HasSmallInductiveDimensionLE.mono {m n : Nat} (hmn : m <= n)
    (H : HasSmallInductiveDimensionLE X m) : HasSmallInductiveDimensionLE X n := by
  apply HasSmallInductiveDimensionLT.mono _ H
  rwa [add_le_add_iff_right]

/--
theorem `HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE` / 定理 `HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE`

English:
theorem HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE
  statement: {n : Nat}
  proof: HasSmallInductiveDimensionLT.mono n.le_succ H

中文:
定理 HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE
  结论: {n : 自然数}
  证明: HasSmallInductiveDimensionLT.mono n.le_succ H

Depends on / 依赖: HasSmallInductiveDimensionLT, HasSmallInductiveDimensionLT.mono, le_succ, n.le_succ
-/
theorem HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE {n : Nat}
    (H : HasSmallInductiveDimensionLT X n) : HasSmallInductiveDimensionLE X n :=
  HasSmallInductiveDimensionLT.mono n.le_succ H

instance (n : Nat) [IsEmpty X] : HasSmallInductiveDimensionLT X n :=
.mono zero_le hasSmallInductiveDimensionLT_zero_iff.2 ‹_›

/-! ### Small inductive dimension -/

variable (X) in
/--
Definition of `smallInductiveDimension` / `smallInductiveDimension` 的定义

English:
definition smallInductiveDimension
  signature: : WithBot Nat∞
  body: sInf {n | forall i : Nat, n < i -> HasSmallInductiveDimensionLT X i}

中文:
定义 smallInductiveDimension
  签名: : WithBot 自然数∞
  定义体: sInf {n | forall i : Nat, n < i -> HasSmallInductiveDimensionLT X i}

Depends on / 依赖: HasSmallInductiveDimensionLT
-/
noncomputable def smallInductiveDimension : WithBot Nat∞ :=
  sInf {n | forall i : Nat, n < i -> HasSmallInductiveDimensionLT X i}

/--
theorem `hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt` / 定理 `hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt`

English:
theorem hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt
  statement: {n : Nat}
  proof: by
  contrapose! h
  simp only [smallInductiveDimension, le_sInf_iff, mem_ofPred_eq]
  intro a ha
  contrapose! ha
  exact ⟨n, ha, h⟩

中文:
定理 hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt
  结论: {n : 自然数}
  证明: by
  contrapose! h
  simp only [smallInductiveDimension, le_sInf_iff, mem_ofPred_eq]
  intro a ha
  contrapose! ha
  exact ⟨n, ha, h⟩
-/
private theorem hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt {n : Nat}
    (h : smallInductiveDimension X < n) : HasSmallInductiveDimensionLT X n := by
  contrapose! h
  simp only [smallInductiveDimension, le_sInf_iff, mem_ofPred_eq]
  intro a ha
  contrapose! ha
  exact ⟨n, ha, h⟩

/--
theorem `hasSmallInductiveDimensionLE_of_smallInductiveDimension_le` / 定理 `hasSmallInductiveDimensionLE_of_smallInductiveDimension_le`

English:
theorem hasSmallInductiveDimensionLE_of_smallInductiveDimension_le
  statement: {n : Nat}
  proof: by
  apply hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt (h.trans_lt _)
  exact_mod_cast n.lt_add_one

中文:
定理 hasSmallInductiveDimensionLE_of_smallInductiveDimension_le
  结论: {n : 自然数}
  证明: by
  apply hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt (h.trans_lt _)
  exact_mod_cast n.lt_add_one
-/
private theorem hasSmallInductiveDimensionLE_of_smallInductiveDimension_le {n : Nat}
    (h : smallInductiveDimension X <= n) : HasSmallInductiveDimensionLE X n := by
  apply hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt (h.trans_lt _)
  exact_mod_cast n.lt_add_one

/--
theorem `smallInductiveDimension_le_iff` / 定理 `smallInductiveDimension_le_iff`

English:
theorem smallInductiveDimension_le_iff
  given: {n : Nat}
  proof: hasSmallInductiveDimensionLE_of_smallInductiveDimension_le
  mpr h := sInf_le fun m hm => .mono (by simpa using hm) h

中文:
定理 smallInductiveDimension_le_iff
  条件: {n : 自然数}
  证明: hasSmallInductiveDimensionLE_of_smallInductiveDimension_le
  mpr h := sInf_le fun m hm => .mono (by simpa using hm) h

Depends on / 依赖: hasSmallInductiveDimensionLE_of_smallInductiveDimension_le
-/
theorem smallInductiveDimension_le_iff {n : Nat} :
    smallInductiveDimension X <= n ↔ HasSmallInductiveDimensionLE X n where
  mp := hasSmallInductiveDimensionLE_of_smallInductiveDimension_le
  mpr h := sInf_le fun m hm => .mono (by simpa using hm) h

/--
theorem `smallInductiveDimension_lt_iff` / 定理 `smallInductiveDimension_lt_iff`

English:
theorem smallInductiveDimension_lt_iff
  given: {n : Nat}
  proof: hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt
  mpr h := by
    cases n with
    | zero =>
      rw [smallInductiveDimension]; rw [csInf_eq_bot_of_bot_mem]
      · simp
      · exact fun _ _ => h.mono zero_le
    | succ n =>
      apply (smallInductiveDimension_le_iff.2 h).trans_lt
      exact_mod_cast n.lt_add_one

中文:
定理 smallInductiveDimension_lt_iff
  条件: {n : 自然数}
  证明: hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt
  mpr h := by
    cases n with
    | zero =>
      rw [smallInductiveDimension]; rw [csInf_eq_bot_of_bot_mem]
      · simp
      · exact fun _ _ => h.mono zero_le
    | succ n =>
      apply (smallInductiveDimension_le_iff.2 h).trans_lt
      exact_mod_cast n.lt_add_one

Depends on / 依赖: hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt
-/
theorem smallInductiveDimension_lt_iff {n : Nat} :
    smallInductiveDimension X < n ↔ HasSmallInductiveDimensionLT X n where
  mp := hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt
  mpr h := by
    cases n with
    | zero =>
      rw [smallInductiveDimension]; rw [csInf_eq_bot_of_bot_mem]
      · simp
      · exact fun _ _ => h.mono zero_le
    | succ n =>
      apply (smallInductiveDimension_le_iff.2 h).trans_lt
      exact_mod_cast n.lt_add_one

variable (X) in
/--
theorem `smallInductiveDimension_le` / 定理 `smallInductiveDimension_le`

English:
theorem smallInductiveDimension_le
  given: (n : Nat) [H : HasSmallInductiveDimensionLE X n]
  proof: smallInductiveDimension_le_iff.2 H

中文:
定理 smallInductiveDimension_le
  条件: (n : 自然数) [H : HasSmallInductiveDimensionLE X n]
  证明: smallInductiveDimension_le_iff.2 H

Depends on / 依赖: smallInductiveDimension_le_iff
-/
theorem smallInductiveDimension_le (n : Nat) [H : HasSmallInductiveDimensionLE X n] :
    smallInductiveDimension X <= n :=
  smallInductiveDimension_le_iff.2 H

variable (X) in
/--
theorem `smallInductiveDimension_lt` / 定理 `smallInductiveDimension_lt`

English:
theorem smallInductiveDimension_lt
  given: (n : Nat) [H : HasSmallInductiveDimensionLT X n]
  proof: smallInductiveDimension_lt_iff.2 H

中文:
定理 smallInductiveDimension_lt
  条件: (n : 自然数) [H : HasSmallInductiveDimensionLT X n]
  证明: smallInductiveDimension_lt_iff.2 H

Depends on / 依赖: smallInductiveDimension_lt_iff
-/
theorem smallInductiveDimension_lt (n : Nat) [H : HasSmallInductiveDimensionLT X n] :
    smallInductiveDimension X < n :=
  smallInductiveDimension_lt_iff.2 H

/--
theorem `smallInductiveDimension_eq` / 定理 `smallInductiveDimension_eq`

English:
theorem smallInductiveDimension_eq
  statement: (n : Nat)
  proof: by
  apply (smallInductiveDimension_le_iff.2 hle).antisymm
  rwa [← not_lt, smallInductiveDimension_lt_iff]

@[simp]

中文:
定理 smallInductiveDimension_eq
  结论: (n : 自然数)
  证明: by
  apply (smallInductiveDimension_le_iff.2 hle).antisymm
  rwa [← not_lt, smallInductiveDimension_lt_iff]

@[simp]

Depends on / 依赖: antisymm, not_lt, smallInductiveDimension_le_iff, smallInductiveDimension_lt_iff
-/
theorem smallInductiveDimension_eq (n : Nat)
    (hle : HasSmallInductiveDimensionLE X n) (hlt : ¬ HasSmallInductiveDimensionLT X n) :
    smallInductiveDimension X = n := by
  apply (smallInductiveDimension_le_iff.2 hle).antisymm
  rwa [← not_lt, smallInductiveDimension_lt_iff]

@[simp]
/--
theorem `smallInductiveDimension_eq_bot` / 定理 `smallInductiveDimension_eq_bot`

English:
theorem smallInductiveDimension_eq_bot
  statement: smallInductiveDimension X = ⊥ ↔ IsEmpty X
  proof: by
  simp_rw [← hasSmallInductiveDimensionLT_zero_iff, ← smallInductiveDimension_lt_iff,
    WithBot.lt_coe_bot.symm, bot_eq_zero', Nat.cast_zero, WithBot.coe_zero]

中文:
定理 smallInductiveDimension_eq_bot
  结论: smallInductiveDimension X = ⊥ ↔ 是空 X
  证明: by
  simp_rw [← hasSmallInductiveDimensionLT_zero_iff, ← smallInductiveDimension_lt_iff,
    WithBot.lt_coe_bot.symm, bot_eq_zero', Nat.cast_zero, WithBot.coe_zero]

Depends on / 依赖: Nat.cast_zero, WithBot, WithBot.coe_zero, WithBot.lt_coe_bot.symm, bot_eq_zero, cast_zero, coe_zero, hasSmallInductiveDimensionLT_zero_iff, lt_coe_bot, simp_rw, smallInductiveDimension_lt_iff
-/
theorem smallInductiveDimension_eq_bot : smallInductiveDimension X = ⊥ ↔ IsEmpty X := by
  simp_rw [← hasSmallInductiveDimensionLT_zero_iff, ← smallInductiveDimension_lt_iff,
    WithBot.lt_coe_bot.symm, bot_eq_zero', Nat.cast_zero, WithBot.coe_zero]

variable (X) in
@[simp]
/--
theorem `smallInductiveDimension_of_isEmpty` / 定理 `smallInductiveDimension_of_isEmpty`

English:
theorem smallInductiveDimension_of_isEmpty
  given: [IsEmpty X]
  statement: smallInductiveDimension X = ⊥
  proof: smallInductiveDimension_eq_bot.2 ‹_›

中文:
定理 smallInductiveDimension_of_isEmpty
  条件: [是空 X]
  结论: smallInductiveDimension X = ⊥
  证明: smallInductiveDimension_eq_bot.2 ‹_›

Depends on / 依赖: smallInductiveDimension_eq_bot
-/
theorem smallInductiveDimension_of_isEmpty [IsEmpty X] : smallInductiveDimension X = ⊥ :=
  smallInductiveDimension_eq_bot.2 ‹_›
