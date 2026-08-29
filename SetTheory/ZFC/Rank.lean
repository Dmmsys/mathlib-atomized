/-
Copyright (c) 2024 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Logic.UnivLE
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.SetTheory.ZFC.Basic

/-!
# Ordinal ranks of PSet and ZFSet

In this file, we define the ordinal ranks of `PSet` and `ZFSet`. These ranks are the same as
`IsWellFounded.rank` over `∈`, but are defined in a way that the universe levels of ranks are the
same as the indexing types.

## Definitions

* `PSet.rank`: Ordinal rank of a pre-set.
* `ZFSet.rank`: Ordinal rank of a ZFC set.
-/

@[expose] public section

universe u v

open Ordinal Order

/-! ### PSet rank -/

namespace PSet

/--
Definition of `rank` / `rank` 的定义

English:
definition rank
  signature: : PSet.{u} -> Ordinal.{u}

中文:
定义 rank
  签名: : PSet.{u} -> Ordinal.{u}
-/
noncomputable def rank : PSet.{u} -> Ordinal.{u}
  | ⟨_, A⟩ => ⨆ a, succ (rank (A a))

/--
theorem `rank_congr` / 定理 `rank_congr`

English:
theorem rank_congr
  statement: forall {x y : PSet}, Equiv x y -> rank x = rank y
  proof: αβ a
      exists b
      rw [← h]; rw [rank_congr h']
    · obtain ⟨b, h'⟩ := βα a
      exists b
      rw [← h]; rw [rank_congr h']

中文:
定理 rank_congr
  结论: 对任意 {x y : PSet}, Equiv x y -> rank x = rank y
  证明: αβ a
      exists b
      rw [← h]; rw [rank_congr h']
    · obtain ⟨b, h'⟩ := βα a
      exists b
      rw [← h]; rw [rank_congr h']
-/
theorem rank_congr : forall {x y : PSet}, Equiv x y -> rank x = rank y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ => by
    apply congr_arg sSup
    ext
    constructor <;> simp only [Set.mem_range, forall_exists_index] <;> intro a h
    · obtain ⟨b, h'⟩ := αβ a
      exists b
      rw [← h]; rw [rank_congr h']
    · obtain ⟨b, h'⟩ := βα a
      exists b
      rw [← h]; rw [rank_congr h']

/--
theorem `rank_lt_of_mem` / 定理 `rank_lt_of_mem`

English:
theorem rank_lt_of_mem
  statement: forall {x y : PSet}, y in x -> rank y < rank x

中文:
定理 rank_lt_of_mem
  结论: 对任意 {x y : PSet}, y in x -> rank y < rank x
-/
theorem rank_lt_of_mem : forall {x y : PSet}, y in x -> rank y < rank x
  | ⟨_, _⟩, _, ⟨_, h⟩ => by
    rw [rank_congr h]; rw [← succ_le_iff]
    apply Ordinal.le_iSup

/--
theorem `rank_le_iff` / 定理 `rank_le_iff`

English:
theorem rank_le_iff
  given: {o : Ordinal}
  statement: forall {x : PSet}, rank x <= o ↔ forall ⦃y⦄, y in x -> rank y < o

中文:
定理 rank_le_iff
  条件: {o : Ordinal}
  结论: 对任意 {x : PSet}, rank x <= o ↔ 对任意 ⦃y⦄, y in x -> rank y < o
-/
theorem rank_le_iff {o : Ordinal} : forall {x : PSet}, rank x <= o ↔ forall ⦃y⦄, y in x -> rank y < o
  | ⟨_, A⟩ => by
    refine ⟨fun h _ h' => (rank_lt_of_mem h').trans_le h, fun h => Ordinal.iSup_le fun a => ?_⟩
    rw [succ_le_iff]
    exact h (Mem.mk A a)

/--
theorem `lt_rank_iff` / 定理 `lt_rank_iff`

English:
theorem lt_rank_iff
  given: {o : Ordinal} {x : PSet}
  statement: o < rank x ↔ exists y in x, o <= rank y
  proof: by
  contrapose!; exact rank_le_iff

中文:
定理 lt_rank_iff
  条件: {o : Ordinal} {x : PSet}
  结论: o < rank x ↔ 存在 y in x, o <= rank y
  证明: by
  contrapose!; exact rank_le_iff

Depends on / 依赖: contrapose, rank_le_iff
-/
theorem lt_rank_iff {o : Ordinal} {x : PSet} : o < rank x ↔ exists y in x, o <= rank y := by
  contrapose!; exact rank_le_iff

variable {x y : PSet.{u}}

/--
theorem `rank_mono` / 定理 `rank_mono`

English:
theorem rank_mono
  given: (h : x subseteq y)
  statement: rank x <= rank y
  proof: rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (mem_of_subset h h₁)

@[simp]

中文:
定理 rank_mono
  条件: (h : x subseteq y)
  结论: rank x <= rank y
  证明: rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (mem_of_subset h h₁)

@[simp]
-/
@[gcongr] theorem rank_mono (h : x subseteq y) : rank x <= rank y :=
  rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (mem_of_subset h h₁)

@[simp]
/--
theorem `rank_empty` / 定理 `rank_empty`

English:
theorem rank_empty
  statement: rank ∅ = 0
  proof: by simp [empty_def, rank]

@[simp]

中文:
定理 rank_empty
  结论: rank ∅ = 0
  证明: by simp [empty_def, rank]

@[simp]

Depends on / 依赖: empty_def
-/
theorem rank_empty : rank ∅ = 0 := by simp [empty_def, rank]

@[simp]
/--
theorem `rank_insert` / 定理 `rank_insert`

English:
theorem rank_insert
  given: (x y : PSet)
  statement: rank (insert x y) = max (succ (rank x)) (rank y)
  proof: by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_insert_iff]
    rintro _ (h | h)
    · simp [rank_congr h]
    · simp [rank_lt_of_mem h]
  · apply max_le
    · exact (rank_lt_of_mem (mem_insert x y)).succ_le
    · exact rank_mono (subset_iff.2 fun z => mem_insert_of_mem x)

@[simp]

中文:
定理 rank_insert
  条件: (x y : PSet)
  结论: rank (insert x y) = max (succ (rank x)) (rank y)
  证明: by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_insert_iff]
    rintro _ (h | h)
    · simp [rank_congr h]
    · simp [rank_lt_of_mem h]
  · apply max_le
    · exact (rank_lt_of_mem (mem_insert x y)).succ_le
    · exact rank_mono (subset_iff.2 fun z => mem_insert_of_mem x)

@[simp]

Depends on / 依赖: le_antisymm, max_le, mem_insert, mem_insert_iff, mem_insert_of_mem, rank_congr, rank_le_iff, rank_lt_of_mem, rank_mono, simp_rw, subset_iff, succ_le
-/
theorem rank_insert (x y : PSet) : rank (insert x y) = max (succ (rank x)) (rank y) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_insert_iff]
    rintro _ (h | h)
    · simp [rank_congr h]
    · simp [rank_lt_of_mem h]
  · apply max_le
    · exact (rank_lt_of_mem (mem_insert x y)).succ_le
    · exact rank_mono (subset_iff.2 fun z => mem_insert_of_mem x)

@[simp]
/--
theorem `rank_singleton` / 定理 `rank_singleton`

English:
theorem rank_singleton
  given: (x : PSet)
  statement: rank {x} = succ (rank x)
  proof: (rank_insert _ _).trans (by simp)

中文:
定理 rank_singleton
  条件: (x : PSet)
  结论: rank {x} = succ (rank x)
  证明: (rank_insert _ _).trans (by simp)

Depends on / 依赖: rank_insert
-/
theorem rank_singleton (x : PSet) : rank {x} = succ (rank x) :=
  (rank_insert _ _).trans (by simp)

/--
theorem `rank_pair` / 定理 `rank_pair`

English:
theorem rank_pair
  given: (x y : PSet)
  statement: rank {x, y} = max (succ (rank x)) (succ (rank y))
  proof: by
  simp

@[simp]

中文:
定理 rank_pair
  条件: (x y : PSet)
  结论: rank {x, y} = max (succ (rank x)) (succ (rank y))
  证明: by
  simp

@[simp]
-/
theorem rank_pair (x y : PSet) : rank {x, y} = max (succ (rank x)) (succ (rank y)) := by
  simp

@[simp]
/--
theorem `rank_powerset` / 定理 `rank_powerset`

English:
theorem rank_powerset
  given: (x : PSet)
  statement: rank (powerset x) = succ (rank x)
  proof: by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_powerset, lt_succ_iff]
    intro
    exact rank_mono
  · rw [succ_le_iff]
    apply rank_lt_of_mem
    simp

中文:
定理 rank_powerset
  条件: (x : PSet)
  结论: rank (powerset x) = succ (rank x)
  证明: by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_powerset, lt_succ_iff]
    intro
    exact rank_mono
  · rw [succ_le_iff]
    apply rank_lt_of_mem
    simp

Depends on / 依赖: le_antisymm, lt_succ_iff, mem_powerset, rank_le_iff, rank_lt_of_mem, rank_mono, simp_rw, succ_le_iff
-/
theorem rank_powerset (x : PSet) : rank (powerset x) = succ (rank x) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_powerset, lt_succ_iff]
    intro
    exact rank_mono
  · rw [succ_le_iff]
    apply rank_lt_of_mem
    simp

/--
theorem `rank_sUnion_le` / 定理 `rank_sUnion_le`

English:
theorem rank_sUnion_le
  given: (x : PSet)
  statement: rank (⋃₀ x) <= rank x
  proof: by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption

中文:
定理 rank_sUnion_le
  条件: (x : PSet)
  结论: rank (⋃₀ x) <= rank x
  证明: by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption

Depends on / 依赖: mem_sUnion, rank_le_iff, rank_lt_of_mem, simp_rw
-/
theorem rank_sUnion_le (x : PSet) : rank (⋃₀ x) <= rank x := by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption

/--
theorem `le_succ_rank_sUnion` / 定理 `le_succ_rank_sUnion`

English:
theorem le_succ_rank_sUnion
  given: (x : PSet)
  statement: rank x <= succ (rank (⋃₀ x))
  proof: by
  rw [← rank_powerset]
  apply rank_mono
  rw [subset_iff]
  intro z _
  rw [mem_powerset]; rw [subset_iff]
  intro _ _
  rw [mem_sUnion]
  exists z

中文:
定理 le_succ_rank_sUnion
  条件: (x : PSet)
  结论: rank x <= succ (rank (⋃₀ x))
  证明: by
  rw [← rank_powerset]
  apply rank_mono
  rw [subset_iff]
  intro z _
  rw [mem_powerset]; rw [subset_iff]
  intro _ _
  rw [mem_sUnion]
  exists z

Depends on / 依赖: mem_powerset, mem_sUnion, rank_mono, rank_powerset, subset_iff
-/
theorem le_succ_rank_sUnion (x : PSet) : rank x <= succ (rank (⋃₀ x)) := by
  rw [← rank_powerset]
  apply rank_mono
  rw [subset_iff]
  intro z _
  rw [mem_powerset]; rw [subset_iff]
  intro _ _
  rw [mem_sUnion]
  exists z

/--
theorem `rank_eq_wfRank` / 定理 `rank_eq_wfRank`

English:
theorem rank_eq_wfRank
  statement: lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := PSet) (· in ·) x
  proof: by
  induction x using mem_wf.induction with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y in x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h


中文:
定理 rank_eq_wfRank
  结论: lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := PSet) (· in ·) x
  证明: by
  induction x using mem_wf.induction with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y in x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h


Depends on / 依赖: IsWellFounded, IsWellFounded.rank_eq, Ordinal, Ordinal.iSup_le, Ordinal.lt_iSup_iff, antisymm, iSup_le, le_of_forall_lt, lt_iSup_iff, lt_lift_iff, lt_rank_iff, mem_wf, mem_wf.induction, rank_eq, rank_lt_of_mem, simp_rw
-/
theorem rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := PSet) (· in ·) x := by
  induction x using mem_wf.induction with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y in x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h
  · simpa using rank_lt_of_mem h.2

end PSet

/-! ### ZFSet rank -/

namespace ZFSet

variable {x y : ZFSet.{u}}

/--
Definition of `rank` / `rank` 的定义

English:
definition rank
  signature: : ZFSet.{u} -> Ordinal.{u}
  body: Quotient.lift _ fun _ _ => PSet.rank_congr

@[simp]

中文:
定义 rank
  签名: : ZFSet.{u} -> Ordinal.{u}
  定义体: Quotient.lift _ fun _ _ => PSet.rank_congr

@[simp]

Depends on / 依赖: PSet.rank_congr, Quotient, Quotient.lift, rank_congr
-/
noncomputable def rank : ZFSet.{u} -> Ordinal.{u} :=
  Quotient.lift _ fun _ _ => PSet.rank_congr

@[simp]
/--
theorem `rank_mk` / 定理 `rank_mk`

English:
theorem rank_mk
  given: (x : PSet)
  statement: rank (.mk x) = x.rank
  proof: rfl

中文:
定理 rank_mk
  条件: (x : PSet)
  结论: rank (.mk x) = x.rank
  证明: rfl
-/
theorem rank_mk (x : PSet) : rank (.mk x) = x.rank :=
  rfl

/--
theorem `rank_lt_of_mem` / 定理 `rank_lt_of_mem`

English:
theorem rank_lt_of_mem
  statement: y in x -> rank y < rank x
  proof: Quotient.inductionOn₂ x y fun _ _ => PSet.rank_lt_of_mem

中文:
定理 rank_lt_of_mem
  结论: y in x -> rank y < rank x
  证明: Quotient.inductionOn₂ x y fun _ _ => PSet.rank_lt_of_mem

Depends on / 依赖: PSet.rank_lt_of_mem, Quotient, Quotient.inductionOn, rank_lt_of_mem
-/
theorem rank_lt_of_mem : y in x -> rank y < rank x :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.rank_lt_of_mem

/--
theorem `rank_le_iff` / 定理 `rank_le_iff`

English:
theorem rank_le_iff
  given: {o : Ordinal}
  statement: rank x <= o ↔ forall ⦃y⦄, y in x -> rank y < o
  proof: ⟨fun h _ h' => (rank_lt_of_mem h').trans_le h,
    Quotient.inductionOn x fun _ h =>
      PSet.rank_le_iff.2 fun y h' => @h ⟦y⟧ h'⟩

中文:
定理 rank_le_iff
  条件: {o : Ordinal}
  结论: rank x <= o ↔ 对任意 ⦃y⦄, y in x -> rank y < o
  证明: ⟨fun h _ h' => (rank_lt_of_mem h').trans_le h,
    Quotient.inductionOn x fun _ h =>
      PSet.rank_le_iff.2 fun y h' => @h ⟦y⟧ h'⟩

Depends on / 依赖: PSet.rank_le_iff, Quotient, Quotient.inductionOn, inductionOn, rank_le_iff, rank_lt_of_mem, trans_le
-/
theorem rank_le_iff {o : Ordinal} : rank x <= o ↔ forall ⦃y⦄, y in x -> rank y < o :=
  ⟨fun h _ h' => (rank_lt_of_mem h').trans_le h,
    Quotient.inductionOn x fun _ h =>
      PSet.rank_le_iff.2 fun y h' => @h ⟦y⟧ h'⟩

/--
theorem `lt_rank_iff` / 定理 `lt_rank_iff`

English:
theorem lt_rank_iff
  given: {o : Ordinal}
  statement: o < rank x ↔ exists y in x, o <= rank y
  proof: by
  contrapose!; exact rank_le_iff

中文:
定理 lt_rank_iff
  条件: {o : Ordinal}
  结论: o < rank x ↔ 存在 y in x, o <= rank y
  证明: by
  contrapose!; exact rank_le_iff

Depends on / 依赖: contrapose, rank_le_iff
-/
theorem lt_rank_iff {o : Ordinal} : o < rank x ↔ exists y in x, o <= rank y := by
  contrapose!; exact rank_le_iff

/--
theorem `rank_mono` / 定理 `rank_mono`

English:
theorem rank_mono
  given: (h : x subseteq y)
  statement: rank x <= rank y
  proof: rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (h h₁)

@[simp]

中文:
定理 rank_mono
  条件: (h : x subseteq y)
  结论: rank x <= rank y
  证明: rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (h h₁)

@[simp]
-/
@[gcongr] theorem rank_mono (h : x subseteq y) : rank x <= rank y :=
  rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (h h₁)

@[simp]
/--
theorem `rank_empty` / 定理 `rank_empty`

English:
theorem rank_empty
  statement: rank ∅ = 0
  proof: PSet.rank_empty

@[simp]

中文:
定理 rank_empty
  结论: rank ∅ = 0
  证明: PSet.rank_empty

@[simp]

Depends on / 依赖: PSet.rank_empty, rank_empty
-/
theorem rank_empty : rank ∅ = 0 := PSet.rank_empty

@[simp]
/--
theorem `rank_insert` / 定理 `rank_insert`

English:
theorem rank_insert
  given: (x y : ZFSet)
  statement: rank (insert x y) = max (succ (rank x)) (rank y)
  proof: Quotient.inductionOn₂ x y PSet.rank_insert

@[simp]

中文:
定理 rank_insert
  条件: (x y : ZFSet)
  结论: rank (insert x y) = max (succ (rank x)) (rank y)
  证明: Quotient.inductionOn₂ x y PSet.rank_insert

@[simp]

Depends on / 依赖: PSet.rank_insert, Quotient, Quotient.inductionOn, rank_insert
-/
theorem rank_insert (x y : ZFSet) : rank (insert x y) = max (succ (rank x)) (rank y) :=
  Quotient.inductionOn₂ x y PSet.rank_insert

@[simp]
/--
theorem `rank_singleton` / 定理 `rank_singleton`

English:
theorem rank_singleton
  given: (x : ZFSet)
  statement: rank {x} = succ (rank x)
  proof: (rank_insert _ _).trans (by simp)

中文:
定理 rank_singleton
  条件: (x : ZFSet)
  结论: rank {x} = succ (rank x)
  证明: (rank_insert _ _).trans (by simp)

Depends on / 依赖: rank_insert
-/
theorem rank_singleton (x : ZFSet) : rank {x} = succ (rank x) :=
  (rank_insert _ _).trans (by simp)

/--
theorem `rank_pair` / 定理 `rank_pair`

English:
theorem rank_pair
  given: (x y : ZFSet)
  statement: rank {x, y} = max (succ (rank x)) (succ (rank y))
  proof: by
  simp

@[simp]

中文:
定理 rank_pair
  条件: (x y : ZFSet)
  结论: rank {x, y} = max (succ (rank x)) (succ (rank y))
  证明: by
  simp

@[simp]
-/
theorem rank_pair (x y : ZFSet) : rank {x, y} = max (succ (rank x)) (succ (rank y)) := by
  simp

@[simp]
/--
theorem `rank_union` / 定理 `rank_union`

English:
theorem rank_union
  given: (x y : ZFSet)
  statement: rank (x union y) = max (rank x) (rank y)
  proof: by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_union, lt_max_iff]
    intro
    apply Or.imp <;> apply rank_lt_of_mem
  · apply max_le <;> apply rank_mono <;> intro _ h <;> simp [h]

@[simp]

中文:
定理 rank_union
  条件: (x y : ZFSet)
  结论: rank (x union y) = max (rank x) (rank y)
  证明: by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_union, lt_max_iff]
    intro
    apply Or.imp <;> apply rank_lt_of_mem
  · apply max_le <;> apply rank_mono <;> intro _ h <;> simp [h]

@[simp]

Depends on / 依赖: Or.imp, le_antisymm, lt_max_iff, max_le, mem_union, rank_le_iff, rank_lt_of_mem, rank_mono, simp_rw
-/
theorem rank_union (x y : ZFSet) : rank (x union y) = max (rank x) (rank y) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_union, lt_max_iff]
    intro
    apply Or.imp <;> apply rank_lt_of_mem
  · apply max_le <;> apply rank_mono <;> intro _ h <;> simp [h]

@[simp]
/--
theorem `rank_powerset` / 定理 `rank_powerset`

English:
theorem rank_powerset
  given: (x : ZFSet)
  statement: rank (powerset x) = succ (rank x)
  proof: Quotient.inductionOn x PSet.rank_powerset

中文:
定理 rank_powerset
  条件: (x : ZFSet)
  结论: rank (powerset x) = succ (rank x)
  证明: Quotient.inductionOn x PSet.rank_powerset

Depends on / 依赖: PSet.rank_powerset, Quotient, Quotient.inductionOn, inductionOn, rank_powerset
-/
theorem rank_powerset (x : ZFSet) : rank (powerset x) = succ (rank x) :=
  Quotient.inductionOn x PSet.rank_powerset

/--
theorem `rank_sUnion_le` / 定理 `rank_sUnion_le`

English:
theorem rank_sUnion_le
  given: (x : ZFSet)
  statement: rank (⋃₀ x) <= rank x
  proof: by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption

中文:
定理 rank_sUnion_le
  条件: (x : ZFSet)
  结论: rank (⋃₀ x) <= rank x
  证明: by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption

Depends on / 依赖: mem_sUnion, rank_le_iff, rank_lt_of_mem, simp_rw
-/
theorem rank_sUnion_le (x : ZFSet) : rank (⋃₀ x) <= rank x := by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption

/--
theorem `le_succ_rank_sUnion` / 定理 `le_succ_rank_sUnion`

English:
theorem le_succ_rank_sUnion
  given: (x : ZFSet)
  statement: rank x <= succ (rank (⋃₀ x))
  proof: by
  rw [← rank_powerset]
  apply rank_mono
  intro z _
  rw [mem_powerset]
  intro _ _
  rw [mem_sUnion]
  exists z

@[simp]

中文:
定理 le_succ_rank_sUnion
  条件: (x : ZFSet)
  结论: rank x <= succ (rank (⋃₀ x))
  证明: by
  rw [← rank_powerset]
  apply rank_mono
  intro z _
  rw [mem_powerset]
  intro _ _
  rw [mem_sUnion]
  exists z

@[simp]

Depends on / 依赖: mem_powerset, mem_sUnion, rank_mono, rank_powerset
-/
theorem le_succ_rank_sUnion (x : ZFSet) : rank x <= succ (rank (⋃₀ x)) := by
  rw [← rank_powerset]
  apply rank_mono
  intro z _
  rw [mem_powerset]
  intro _ _
  rw [mem_sUnion]
  exists z

@[simp]
/--
theorem `rank_range` / 定理 `rank_range`

English:
theorem rank_range
  given: {α : Type*} [Small.{u} α] (f : α -> ZFSet.{u})
  proof: by
  apply (Ordinal.iSup_le _).antisymm'
  · simpa [rank_le_iff, ← add_one_le_iff] using Ordinal.le_iSup _
  · simp [rank_lt_of_mem]

@[simp]

中文:
定理 rank_range
  条件: {α : 类型} [Small.{u} α] (f : α -> ZFSet.{u})
  证明: by
  apply (Ordinal.iSup_le _).antisymm'
  · simpa [rank_le_iff, ← add_one_le_iff] using Ordinal.le_iSup _
  · simp [rank_lt_of_mem]

@[simp]

Depends on / 依赖: Ordinal, Ordinal.iSup_le, Ordinal.le_iSup, add_one_le_iff, antisymm, iSup_le, le_iSup, rank_le_iff, rank_lt_of_mem
-/
theorem rank_range {α : Type*} [Small.{u} α] (f : α -> ZFSet.{u}) :
    rank (range f) = ⨆ i, succ (rank (f i)) := by
  apply (Ordinal.iSup_le _).antisymm'
  · simpa [rank_le_iff, ← add_one_le_iff] using Ordinal.le_iSup _
  · simp [rank_lt_of_mem]

@[simp]
/--
theorem `rank_iUnion` / 定理 `rank_iUnion`

English:
theorem rank_iUnion
  given: {α : Type*} [Small.{u} α] (f : α -> ZFSet.{u})
  proof: by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_iUnion]
    intro y ⟨i, hy⟩
    exact (rank_lt_of_mem hy).trans_le (Ordinal.le_iSup _ _)
  · exact Ordinal.iSup_le fun i => rank_mono (subset_iUnion f i)

中文:
定理 rank_iUnion
  条件: {α : 类型} [Small.{u} α] (f : α -> ZFSet.{u})
  证明: by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_iUnion]
    intro y ⟨i, hy⟩
    exact (rank_lt_of_mem hy).trans_le (Ordinal.le_iSup _ _)
  · exact Ordinal.iSup_le fun i => rank_mono (subset_iUnion f i)

Depends on / 依赖: Ordinal, Ordinal.iSup_le, Ordinal.le_iSup, iSup_le, le_antisymm, le_iSup, mem_iUnion, rank_le_iff, rank_lt_of_mem, rank_mono, simp_rw, subset_iUnion, trans_le
-/
theorem rank_iUnion {α : Type*} [Small.{u} α] (f : α -> ZFSet.{u}) :
    rank (⋃ i, f i) = ⨆ i, rank (f i) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_iUnion]
    intro y ⟨i, hy⟩
    exact (rank_lt_of_mem hy).trans_le (Ordinal.le_iSup _ _)
  · exact Ordinal.iSup_le fun i => rank_mono (subset_iUnion f i)

/--
theorem `rank_eq_wfRank` / 定理 `rank_eq_wfRank`

English:
theorem rank_eq_wfRank
  statement: lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := ZFSet) (· in ·) x
  proof: by
  induction x using inductionOn with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y in x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h
  · s

中文:
定理 rank_eq_wfRank
  结论: lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := ZFSet) (· in ·) x
  证明: by
  induction x using inductionOn with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y in x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h
  · s

Depends on / 依赖: IsWellFounded, IsWellFounded.rank_eq, Ordinal, Ordinal.iSup_le, Ordinal.lt_iSup_iff, antisymm, iSup_le, inductionOn, le_of_forall_lt, lt_iSup_iff, lt_lift_iff, lt_rank_iff, rank_eq, rank_lt_of_mem, simp_rw
-/
theorem rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := ZFSet) (· in ·) x := by
  induction x using inductionOn with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y in x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h
  · simpa using rank_lt_of_mem h.2

end ZFSet
