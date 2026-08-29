/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Order.Interval.Set.OrderIso
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Principal upper/lower sets

The results in this file all assume that the underlying type is equipped with at least a preorder.

## Main declarations

* `UpperSet.Ici`: Principal upper set. `Set.Ici` as an upper set.
* `UpperSet.Ioi`: Strict principal upper set. `Set.Ioi` as an upper set.
* `LowerSet.Iic`: Principal lower set. `Set.Iic` as a lower set.
* `LowerSet.Iio`: Strict principal lower set. `Set.Iio` as a lower set.
-/

@[expose] public section

open Function Set

variable {α β : Type*} {ι : Sort*} {κ : ι -> Sort*}

namespace UpperSet

section Preorder

variable [Preorder α] [Preorder β] {s : UpperSet α} {a b : α}

/-- Principal upper set. `Set.Ici` as an upper set. The smallest upper set containing a given
element. -/
@[to_dual
/-- Principal lower set. `Set.Iic` as a lower set. The smallest lower set containing a given
element. -/]
/--
Definition of `Ici` / `Ici` 的定义

English:
definition Ici
  signature: (a : α)
  body: ⟨Set.Ici a, isUpperSet_Ici a⟩

中文:
定义 左闭右无界区间
  签名: (a : α)
  定义体: ⟨Set.Ici a, isUpperSet_Ici a⟩

Depends on / 依赖: Set.Ici, isUpperSet_Ici
-/
def Ici (a : α) : UpperSet α :=
  ⟨Set.Ici a, isUpperSet_Ici a⟩

/-- Strict principal upper set. `Set.Ioi` as an upper set. -/
@[to_dual
/-- Strict principal lower set. `Set.Iio` as a lower set. -/]
/--
Definition of `Ioi` / `Ioi` 的定义

English:
definition Ioi
  signature: (a : α)
  body: ⟨Set.Ioi a, isUpperSet_Ioi a⟩

@[to_dual (attr := simp)]

中文:
定义 左开右无界区间
  签名: (a : α)
  定义体: ⟨Set.Ioi a, isUpperSet_Ioi a⟩

@[to_dual (attr := simp)]

Depends on / 依赖: Set.Ioi, isUpperSet_Ioi
-/
def Ioi (a : α) : UpperSet α :=
  ⟨Set.Ioi a, isUpperSet_Ioi a⟩

@[to_dual (attr := simp)]
/--
theorem `coe_Ici` / 定理 `coe_Ici`

English:
theorem coe_Ici
  given: (a : α)
  statement: ↑(Ici a) = Set.Ici a
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_Ici
  条件: (a : α)
  结论: ↑(左闭右无界区间 a) = 集合.左闭右无界区间 a
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_Ici (a : α) : ↑(Ici a) = Set.Ici a :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `coe_Ioi` / 定理 `coe_Ioi`

English:
theorem coe_Ioi
  given: (a : α)
  statement: ↑(Ioi a) = Set.Ioi a
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_Ioi
  条件: (a : α)
  结论: ↑(左开右无界区间 a) = 集合.左开右无界区间 a
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_Ioi (a : α) : ↑(Ioi a) = Set.Ioi a :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `mem_Ici_iff` / 定理 `mem_Ici_iff`

English:
theorem mem_Ici_iff
  statement: b in Ici a ↔ a <= b
  proof: Iff.rfl

@[to_dual (attr := simp)]

中文:
定理 mem_Ici_iff
  结论: b in 左闭右无界区间 a ↔ a <= b
  证明: Iff.rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_Ici_iff : b in Ici a ↔ a <= b :=
  Iff.rfl

@[to_dual (attr := simp)]
/--
theorem `mem_Ioi_iff` / 定理 `mem_Ioi_iff`

English:
theorem mem_Ioi_iff
  statement: b in Ioi a ↔ a < b
  proof: Iff.rfl

@[to_dual (attr := simp)]

中文:
定理 mem_Ioi_iff
  结论: b in 左开右无界区间 a ↔ a < b
  证明: Iff.rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_Ioi_iff : b in Ioi a ↔ a < b :=
  Iff.rfl

@[to_dual (attr := simp)]
/--
theorem `map_Ici` / 定理 `map_Ici`

English:
theorem map_Ici
  given: (f : α ≃o β) (a : α)
  statement: map f (Ici a) = Ici (f a)
  proof: by
  ext
  simp

@[to_dual (attr := simp)]

中文:
定理 map_Ici
  条件: (f : α ≃o β) (a : α)
  结论: map f (左闭右无界区间 a) = 左闭右无界区间 (f a)
  证明: by
  ext
  simp

@[to_dual (attr := simp)]
-/
theorem map_Ici (f : α ≃o β) (a : α) : map f (Ici a) = Ici (f a) := by
  ext
  simp

@[to_dual (attr := simp)]
/--
theorem `map_Ioi` / 定理 `map_Ioi`

English:
theorem map_Ioi
  given: (f : α ≃o β) (a : α)
  statement: map f (Ioi a) = Ioi (f a)
  proof: by
  ext
  simp

@[to_dual Ioi_le_Ici]

中文:
定理 map_Ioi
  条件: (f : α ≃o β) (a : α)
  结论: map f (左开右无界区间 a) = 左开右无界区间 (f a)
  证明: by
  ext
  simp

@[to_dual Ioi_le_Ici]
-/
theorem map_Ioi (f : α ≃o β) (a : α) : map f (Ioi a) = Ioi (f a) := by
  ext
  simp

@[to_dual Ioi_le_Ici]
/--
theorem `Ici_le_Ioi` / 定理 `Ici_le_Ioi`

English:
theorem Ici_le_Ioi
  given: (a : α)
  statement: Ici a <= Ioi a
  proof: Ioi_subset_Ici_self

@[to_dual (attr := simp)]
nonrec theorem Ici_bot [OrderBot α] : Ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot

@[to_dual (attr := simp)]
nonrec theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top

@[to_dual (attr := simp)]

中文:
定理 Ici_le_Ioi
  条件: (a : α)
  结论: 左闭右无界区间 a <= 左开右无界区间 a
  证明: Ioi_subset_Ici_self

@[to_dual (attr := simp)]
nonrec theorem Ici_bot [OrderBot α] : Ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot

@[to_dual (attr := simp)]
nonrec theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top

@[to_dual (attr := simp)]

Depends on / 依赖: Ioi_subset_Ici_self
-/
theorem Ici_le_Ioi (a : α) : Ici a <= Ioi a :=
  Ioi_subset_Ici_self

@[to_dual (attr := simp)]
nonrec theorem Ici_bot [OrderBot α] : Ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot

@[to_dual (attr := simp)]
nonrec theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top

@[to_dual (attr := simp)]
/--
lemma `Ici_ne_top` / 引理 `Ici_ne_top`

English:
lemma Ici_ne_top
  statement: Ici a != ⊤
  proof: SetLike.coe_ne_coe.1 nonempty_Ici.ne_empty

@[to_dual (attr := simp) bot_lt_Iic]

中文:
引理 Ici_ne_top
  结论: 左闭右无界区间 a != ⊤
  证明: SetLike.coe_ne_coe.1 nonempty_Ici.ne_empty

@[to_dual (attr := simp) bot_lt_Iic]

Depends on / 依赖: SetLike, SetLike.coe_ne_coe, coe_ne_coe, ne_empty, nonempty_Ici, nonempty_Ici.ne_empty
-/
lemma Ici_ne_top : Ici a != ⊤ := SetLike.coe_ne_coe.1 nonempty_Ici.ne_empty

@[to_dual (attr := simp) bot_lt_Iic]
/--
lemma `Ici_lt_top` / 引理 `Ici_lt_top`

English:
lemma Ici_lt_top
  statement: Ici a < ⊤
  proof: lt_top_iff_ne_top.2 Ici_ne_top

@[to_dual (attr := simp) Iic_le]

中文:
引理 Ici_lt_top
  结论: 左闭右无界区间 a < ⊤
  证明: lt_top_iff_ne_top.2 Ici_ne_top

@[to_dual (attr := simp) Iic_le]

Depends on / 依赖: Ici_ne_top, lt_top_iff_ne_top
-/
lemma Ici_lt_top : Ici a < ⊤ := lt_top_iff_ne_top.2 Ici_ne_top

@[to_dual (attr := simp) Iic_le]
/--
lemma `le_Ici` / 引理 `le_Ici`

English:
lemma le_Ici
  statement: s <= Ici a ↔ a in s
  proof: ⟨fun h => h le_rfl, fun ha => s.upper.Ici_subset ha⟩

中文:
引理 le_Ici
  结论: s <= 左闭右无界区间 a ↔ a in s
  证明: ⟨fun h => h le_rfl, fun ha => s.upper.Ici_subset ha⟩

Depends on / 依赖: Ici_subset, le_rfl, s.upper.Ici_subset
-/
lemma le_Ici : s <= Ici a ↔ a in s := ⟨fun h => h le_rfl, fun ha => s.upper.Ici_subset ha⟩

variable (α) in
@[to_dual]
/--
theorem `Ici_strictMono` / 定理 `Ici_strictMono`

English:
theorem Ici_strictMono
  statement: StrictMono (Ici (α := α))
  proof: fun _ _ h => (Set.Ici_ssubset_Ici).mpr h

中文:
定理 Ici_strictMono
  结论: 严格递增 (左闭右无界区间 (α := α))
  证明: fun _ _ h => (Set.Ici_ssubset_Ici).mpr h

Depends on / 依赖: Ici_ssubset_Ici, Set.Ici_ssubset_Ici
-/
theorem Ici_strictMono : StrictMono (Ici (α := α)) := fun _ _ h => (Set.Ici_ssubset_Ici).mpr h

variable (α) in
@[to_dual]
/--
theorem `Ioi_strictMono` / 定理 `Ioi_strictMono`

English:
theorem Ioi_strictMono
  statement: StrictMono (Ioi (α := α))
  proof: fun _ _ h => Set.Ioi_ssubset_Ioi h

中文:
定理 Ioi_strictMono
  结论: 严格递增 (左开右无界区间 (α := α))
  证明: fun _ _ h => Set.Ioi_ssubset_Ioi h

Depends on / 依赖: Ioi_ssubset_Ioi, Set.Ioi_ssubset_Ioi
-/
theorem Ioi_strictMono : StrictMono (Ioi (α := α)) := fun _ _ h => Set.Ioi_ssubset_Ioi h

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

@[to_dual]
/--
lemma `Ici_injective` / 引理 `Ici_injective`

English:
lemma Ici_injective
  statement: Injective (Ici : α -> UpperSet α)
  proof: fun _a _b hab =>
Set.Ici_injective congr_arg ((↑) : _ -> Set α) hab

@[to_dual (attr := simp)]

中文:
引理 Ici_injective
  结论: 单射 (左闭右无界区间 : α -> 上集 α)
  证明: fun _a _b hab =>
Set.Ici_injective congr_arg ((↑) : _ -> Set α) hab

@[to_dual (attr := simp)]
-/
lemma Ici_injective : Injective (Ici : α -> UpperSet α) := fun _a _b hab =>
Set.Ici_injective congr_arg ((↑) : _ -> Set α) hab

@[to_dual (attr := simp)]
/--
lemma `Ici_inj` / 引理 `Ici_inj`

English:
lemma Ici_inj
  statement: Ici a = Ici b ↔ a = b
  proof: Ici_injective.eq_iff

@[to_dual]

中文:
引理 Ici_inj
  结论: 左闭右无界区间 a = 左闭右无界区间 b ↔ a = b
  证明: Ici_injective.eq_iff

@[to_dual]

Depends on / 依赖: Ici_injective, Ici_injective.eq_iff, eq_iff
-/
lemma Ici_inj : Ici a = Ici b ↔ a = b := Ici_injective.eq_iff

@[to_dual]
/--
lemma `Ici_ne_Ici` / 引理 `Ici_ne_Ici`

English:
lemma Ici_ne_Ici
  statement: Ici a != Ici b ↔ a != b
  proof: Ici_inj.not

@[to_dual (attr := simp)]

中文:
引理 Ici_ne_Ici
  结论: 左闭右无界区间 a != 左闭右无界区间 b ↔ a != b
  证明: Ici_inj.not

@[to_dual (attr := simp)]

Depends on / 依赖: Ici_inj, Ici_inj.not
-/
lemma Ici_ne_Ici : Ici a != Ici b ↔ a != b := Ici_inj.not

@[to_dual (attr := simp)]
/--
theorem `Ioi_eq_top` / 定理 `Ioi_eq_top`

English:
theorem Ioi_eq_top
  given: [OrderTop α] {a : α}
  statement: Ioi a = ⊤ ↔ a = ⊤
  proof: by
  simp [UpperSet.ext_iff]

中文:
定理 Ioi_eq_top
  条件: [有顶序 α] {a : α}
  结论: 左开右无界区间 a = ⊤ ↔ a = ⊤
  证明: by
  simp [UpperSet.ext_iff]

Depends on / 依赖: UpperSet, UpperSet.ext_iff, ext_iff
-/
theorem Ioi_eq_top [OrderTop α] {a : α} : Ioi a = ⊤ ↔ a = ⊤ := by
  simp [UpperSet.ext_iff]

end PartialOrder

@[to_dual (attr := simp)]
/--
theorem `Ici_sup` / 定理 `Ici_sup`

English:
theorem Ici_sup
  given: [SemilatticeSup α] (a b : α)
  statement: Ici (a ⊔ b) = Ici a ⊔ Ici b
  proof: ext Ici_inter_Ici.symm

中文:
定理 Ici_sup
  条件: [SemilatticeSup α] (a b : α)
  结论: 左闭右无界区间 (a ⊔ b) = 左闭右无界区间 a ⊔ 左闭右无界区间 b
  证明: ext Ici_inter_Ici.symm

Depends on / 依赖: Ici_inter_Ici, Ici_inter_Ici.symm
-/
theorem Ici_sup [SemilatticeSup α] (a b : α) : Ici (a ⊔ b) = Ici a ⊔ Ici b :=
  ext Ici_inter_Ici.symm

section CompleteLattice

variable [CompleteLattice α]

@[to_dual (attr := simp)]
/--
theorem `Ici_sSup` / 定理 `Ici_sSup`

English:
theorem Ici_sSup
  given: (S : Set α)
  statement: Ici (sSup S) = ⨆ a in S, Ici a
  proof: SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, sSup_le_iff]

@[to_dual (attr := simp)]

中文:
定理 Ici_sSup
  条件: (S : 集合 α)
  结论: 左闭右无界区间 (sSup S) = ⨆ a in S, 左闭右无界区间 a
  证明: SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, sSup_le_iff]

@[to_dual (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext, mem_Ici_iff, mem_iSup_iff, sSup_le_iff
-/
theorem Ici_sSup (S : Set α) : Ici (sSup S) = ⨆ a in S, Ici a :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, sSup_le_iff]

@[to_dual (attr := simp)]
/--
theorem `Ici_iSup` / 定理 `Ici_iSup`

English:
theorem Ici_iSup
  given: (f : ι -> α)
  statement: Ici (⨆ i, f i) = ⨆ i, Ici (f i)
  proof: SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, iSup_le_iff]

@[to_dual]

中文:
定理 Ici_iSup
  条件: (f : ι -> α)
  结论: 左闭右无界区间 (⨆ i, f i) = ⨆ i, 左闭右无界区间 (f i)
  证明: SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, iSup_le_iff]

@[to_dual]

Depends on / 依赖: SetLike, SetLike.ext, iSup_le_iff, mem_Ici_iff, mem_iSup_iff
-/
theorem Ici_iSup (f : ι -> α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i) :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, iSup_le_iff]

@[to_dual]
/--
theorem `Ici_iSup₂` / 定理 `Ici_iSup₂`

English:
theorem Ici_iSup₂
  given: (f : forall i, κ i -> α)
  statement: Ici (⨆ (i) (j), f i j) = ⨆ (i) (j), Ici (f i j)
  proof: by
  simp

中文:
定理 Ici_iSup₂
  条件: (f : 对任意 i, κ i -> α)
  结论: 左闭右无界区间 (⨆ (i) (j), f i j) = ⨆ (i) (j), 左闭右无界区间 (f i j)
  证明: by
  simp
-/
theorem Ici_iSup₂ (f : forall i, κ i -> α) : Ici (⨆ (i) (j), f i j) = ⨆ (i) (j), Ici (f i j) := by
  simp

end CompleteLattice

end UpperSet
