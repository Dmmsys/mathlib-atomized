/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Set.OrderEmbedding
public import Mathlib.Order.SetNotation
public import Mathlib.Order.WellFounded

/-!
# Properties of unbundled upper/lower sets

This file proves results on `IsUpperSet` and `IsLowerSet`, including their interactions with
set operations, images, preimages and order duals, and properties that reflect stronger assumptions
on the underlying order (such as `PartialOrder` and `LinearOrder`).

## TODO

* Lattice structure on antichains.
* Order equivalence between upper/lower sets and antichains.
-/

public section

open OrderDual Set

variable {α β : Type*} {ι : Sort*} {κ : ι -> Sort*}

attribute [aesop norm unfold] IsUpperSet IsLowerSet

section LE

variable [LE α] {s t : Set α} {a : α}

@[to_dual]
/--
theorem `isUpperSet_empty` / 定理 `isUpperSet_empty`

English:
theorem isUpperSet_empty
  statement: IsUpperSet (∅ : Set α)
  proof: fun _ _ _ => id

@[to_dual]

中文:
定理 isUpperSet_empty
  结论: 是上集 (∅ : 集合 α)
  证明: fun _ _ _ => id

@[to_dual]
-/
theorem isUpperSet_empty : IsUpperSet (∅ : Set α) := fun _ _ _ => id

@[to_dual]
/--
theorem `isUpperSet_univ` / 定理 `isUpperSet_univ`

English:
theorem isUpperSet_univ
  statement: IsUpperSet (univ : Set α)
  proof: fun _ _ _ => id

@[to_dual]

中文:
定理 isUpperSet_univ
  结论: 是上集 (univ : 集合 α)
  证明: fun _ _ _ => id

@[to_dual]
-/
theorem isUpperSet_univ : IsUpperSet (univ : Set α) := fun _ _ _ => id

@[to_dual]
/--
theorem `IsUpperSet.compl` / 定理 `IsUpperSet.compl`

English:
theorem IsUpperSet.compl
  given: (hs : IsUpperSet s)
  statement: IsLowerSet sᶜ
  proof: fun _a _b h hb ha => hb hs h ha

@[to_dual (attr := simp)]

中文:
定理 是上集.compl
  条件: (hs : 是上集 s)
  结论: 是下集 sᶜ
  证明: fun _a _b h hb ha => hb hs h ha

@[to_dual (attr := simp)]
-/
theorem IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet sᶜ := fun _a _b h hb ha => hb hs h ha

@[to_dual (attr := simp)]
/--
theorem `isUpperSet_compl` / 定理 `isUpperSet_compl`

English:
theorem isUpperSet_compl
  statement: IsUpperSet sᶜ ↔ IsLowerSet s
  proof: ⟨fun h => by
    convert! h.compl
    rw [compl_compl], IsLowerSet.compl⟩

@[to_dual]

中文:
定理 isUpperSet_compl
  结论: 是上集 sᶜ ↔ 是下集 s
  证明: ⟨fun h => by
    convert! h.compl
    rw [compl_compl], IsLowerSet.compl⟩

@[to_dual]

Depends on / 依赖: IsLowerSet, IsLowerSet.compl, compl_compl, convert, h.compl
-/
theorem isUpperSet_compl : IsUpperSet sᶜ ↔ IsLowerSet s :=
  ⟨fun h => by
    convert! h.compl
    rw [compl_compl], IsLowerSet.compl⟩

@[to_dual]
/--
theorem `IsUpperSet.union` / 定理 `IsUpperSet.union`

English:
theorem IsUpperSet.union
  given: (hs : IsUpperSet s) (ht : IsUpperSet t)
  statement: IsUpperSet (s union t)
  proof: fun _ _ h => Or.imp (hs h) (ht h)

@[to_dual]

中文:
定理 是上集.union
  条件: (hs : 是上集 s) (ht : 是上集 t)
  结论: 是上集 (s union t)
  证明: fun _ _ h => Or.imp (hs h) (ht h)

@[to_dual]

Depends on / 依赖: Or.imp
-/
theorem IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s union t) :=
  fun _ _ h => Or.imp (hs h) (ht h)

@[to_dual]
/--
theorem `IsUpperSet.inter` / 定理 `IsUpperSet.inter`

English:
theorem IsUpperSet.inter
  given: (hs : IsUpperSet s) (ht : IsUpperSet t)
  statement: IsUpperSet (s inter t)
  proof: fun _ _ h => And.imp (hs h) (ht h)

@[to_dual]

中文:
定理 是上集.inter
  条件: (hs : 是上集 s) (ht : 是上集 t)
  结论: 是上集 (s inter t)
  证明: fun _ _ h => And.imp (hs h) (ht h)

@[to_dual]

Depends on / 依赖: And.imp
-/
theorem IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s inter t) :=
  fun _ _ h => And.imp (hs h) (ht h)

@[to_dual]
/--
theorem `isUpperSet_sUnion` / 定理 `isUpperSet_sUnion`

English:
theorem isUpperSet_sUnion
  given: {S : Set (Set α)} (hf : forall s in S, IsUpperSet s)
  statement: IsUpperSet (⋃₀ S)
  proof: fun _ _ h => Exists.imp fun _ hs => ⟨hs.1, hf _ hs.1 h hs.2⟩

@[to_dual]

中文:
定理 isUpperSet_sUnion
  条件: {S : 集合 (集合 α)} (hf : 对任意 s in S, 是上集 s)
  结论: 是上集 (⋃₀ S)
  证明: fun _ _ h => Exists.imp fun _ hs => ⟨hs.1, hf _ hs.1 h hs.2⟩

@[to_dual]

Depends on / 依赖: Exists, Exists.imp
-/
theorem isUpperSet_sUnion {S : Set (Set α)} (hf : forall s in S, IsUpperSet s) : IsUpperSet (⋃₀ S) :=
  fun _ _ h => Exists.imp fun _ hs => ⟨hs.1, hf _ hs.1 h hs.2⟩

@[to_dual]
/--
theorem `isUpperSet_iUnion` / 定理 `isUpperSet_iUnion`

English:
theorem isUpperSet_iUnion
  given: {f : ι -> Set α} (hf : forall i, IsUpperSet (f i))
  statement: IsUpperSet (⋃ i, f i)
  proof: isUpperSet_sUnion forall_mem_range.2 hf

@[to_dual]

中文:
定理 isUpperSet_iUnion
  条件: {f : ι -> 集合 α} (hf : 对任意 i, 是上集 (f i))
  结论: 是上集 (⋃ i, f i)
  证明: isUpperSet_sUnion forall_mem_range.2 hf

@[to_dual]

Depends on / 依赖: forall_mem_range, isUpperSet_sUnion
-/
theorem isUpperSet_iUnion {f : ι -> Set α} (hf : forall i, IsUpperSet (f i)) : IsUpperSet (⋃ i, f i) :=
isUpperSet_sUnion forall_mem_range.2 hf

@[to_dual]
/--
theorem `isUpperSet_iUnion₂` / 定理 `isUpperSet_iUnion₂`

English:
theorem isUpperSet_iUnion₂
  given: {f : forall i, κ i -> Set α} (hf : forall i j, IsUpperSet (f i j))
  proof: isUpperSet_iUnion fun i => isUpperSet_iUnion hf i

@[to_dual]

中文:
定理 isUpperSet_iUnion₂
  条件: {f : 对任意 i, κ i -> 集合 α} (hf : 对任意 i j, 是上集 (f i j))
  证明: isUpperSet_iUnion fun i => isUpperSet_iUnion hf i

@[to_dual]

Depends on / 依赖: isUpperSet_iUnion
-/
theorem isUpperSet_iUnion₂ {f : forall i, κ i -> Set α} (hf : forall i j, IsUpperSet (f i j)) :
    IsUpperSet (⋃ (i) (j), f i j) :=
isUpperSet_iUnion fun i => isUpperSet_iUnion hf i

@[to_dual]
/--
theorem `isUpperSet_sInter` / 定理 `isUpperSet_sInter`

English:
theorem isUpperSet_sInter
  given: {S : Set (Set α)} (hf : forall s in S, IsUpperSet s)
  statement: IsUpperSet (⋂₀ S)
  proof: fun _ _ h => forall₂_imp fun s hs => hf s hs h

@[to_dual]

中文:
定理 isUpperSet_s整数er
  条件: {S : 集合 (集合 α)} (hf : 对任意 s in S, 是上集 s)
  结论: 是上集 (⋂₀ S)
  证明: fun _ _ h => forall₂_imp fun s hs => hf s hs h

@[to_dual]
-/
theorem isUpperSet_sInter {S : Set (Set α)} (hf : forall s in S, IsUpperSet s) : IsUpperSet (⋂₀ S) :=
  fun _ _ h => forall₂_imp fun s hs => hf s hs h

@[to_dual]
/--
theorem `isUpperSet_iInter` / 定理 `isUpperSet_iInter`

English:
theorem isUpperSet_iInter
  given: {f : ι -> Set α} (hf : forall i, IsUpperSet (f i))
  statement: IsUpperSet (⋂ i, f i)
  proof: isUpperSet_sInter forall_mem_range.2 hf

@[to_dual]

中文:
定理 isUpperSet_i整数er
  条件: {f : ι -> 集合 α} (hf : 对任意 i, 是上集 (f i))
  结论: 是上集 (⋂ i, f i)
  证明: isUpperSet_sInter forall_mem_range.2 hf

@[to_dual]

Depends on / 依赖: forall_mem_range, isUpperSet_sInter
-/
theorem isUpperSet_iInter {f : ι -> Set α} (hf : forall i, IsUpperSet (f i)) : IsUpperSet (⋂ i, f i) :=
isUpperSet_sInter forall_mem_range.2 hf

@[to_dual]
/--
theorem `isUpperSet_iInter₂` / 定理 `isUpperSet_iInter₂`

English:
theorem isUpperSet_iInter₂
  given: {f : forall i, κ i -> Set α} (hf : forall i j, IsUpperSet (f i j))
  proof: isUpperSet_iInter fun i => isUpperSet_iInter hf i

@[to_dual (attr := simp)]

中文:
定理 isUpperSet_i整数er₂
  条件: {f : 对任意 i, κ i -> 集合 α} (hf : 对任意 i j, 是上集 (f i j))
  证明: isUpperSet_iInter fun i => isUpperSet_iInter hf i

@[to_dual (attr := simp)]

Depends on / 依赖: isUpperSet_iInter
-/
theorem isUpperSet_iInter₂ {f : forall i, κ i -> Set α} (hf : forall i j, IsUpperSet (f i j)) :
    IsUpperSet (⋂ (i) (j), f i j) :=
isUpperSet_iInter fun i => isUpperSet_iInter hf i

@[to_dual (attr := simp)]
/--
theorem `isUpperSet_preimage_ofDual_iff` / 定理 `isUpperSet_preimage_ofDual_iff`

English:
theorem isUpperSet_preimage_ofDual_iff
  statement: IsUpperSet (ofDual ⁻¹' s) ↔ IsLowerSet s
  proof: Iff.rfl

@[to_dual (attr := simp)]

中文:
定理 isUpperSet_preimage_ofDual_iff
  结论: 是上集 (ofDual ⁻¹' s) ↔ 是下集 s
  证明: Iff.rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem isUpperSet_preimage_ofDual_iff : IsUpperSet (ofDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

@[to_dual (attr := simp)]
/--
theorem `isUpperSet_preimage_toDual_iff` / 定理 `isUpperSet_preimage_toDual_iff`

English:
theorem isUpperSet_preimage_toDual_iff
  given: {s : Set αᵒᵈ}
  statement: IsUpperSet (toDual ⁻¹' s) ↔ IsLowerSet s
  proof: Iff.rfl

@[to_dual] alias ⟨_, IsUpperSet.toDual⟩ := isLowerSet_preimage_ofDual_iff
@[to_dual] alias ⟨_, IsUpperSet.ofDual⟩ := isLowerSet_preimage_toDual_iff

@[to_dual]

中文:
定理 isUpperSet_preimage_toDual_iff
  条件: {s : 集合 αᵒᵈ}
  结论: 是上集 (toDual ⁻¹' s) ↔ 是下集 s
  证明: Iff.rfl

@[to_dual] alias ⟨_, IsUpperSet.toDual⟩ := isLowerSet_preimage_ofDual_iff
@[to_dual] alias ⟨_, IsUpperSet.ofDual⟩ := isLowerSet_preimage_toDual_iff

@[to_dual]

Depends on / 依赖: Iff.rfl
-/
theorem isUpperSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsUpperSet (toDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

@[to_dual] alias ⟨_, IsUpperSet.toDual⟩ := isLowerSet_preimage_ofDual_iff
@[to_dual] alias ⟨_, IsUpperSet.ofDual⟩ := isLowerSet_preimage_toDual_iff

@[to_dual]
/--
lemma `IsUpperSet.isLowerSet_preimage_coe` / 引理 `IsUpperSet.isLowerSet_preimage_coe`

English:
lemma IsUpperSet.isLowerSet_preimage_coe
  given: (hs : IsUpperSet s)
  proof: by aesop

@[to_dual]

中文:
引理 是上集.isLowerSet_preimage_coe
  条件: (hs : 是上集 s)
  证明: by aesop

@[to_dual]
-/
lemma IsUpperSet.isLowerSet_preimage_coe (hs : IsUpperSet s) :
    IsLowerSet ((↑) ⁻¹' t : Set s) ↔ forall b in s, forall c in t, b <= c -> b in t := by aesop

@[to_dual]
/--
lemma `IsUpperSet.sdiff` / 引理 `IsUpperSet.sdiff`

English:
lemma IsUpperSet.sdiff
  given: (hs : IsUpperSet s) (ht : forall b in s, forall c in t, b <= c -> b in t)
  proof: fun _b _c hbc hb => ⟨hs hbc hb.1, fun hc => hb.2 ht _ hb.1 _ hc hbc⟩

@[to_dual]

中文:
引理 是上集.sdiff
  条件: (hs : 是上集 s) (ht : 对任意 b in s, 对任意 c in t, b <= c -> b in t)
  证明: fun _b _c hbc hb => ⟨hs hbc hb.1, fun hc => hb.2 ht _ hb.1 _ hc hbc⟩

@[to_dual]
-/
lemma IsUpperSet.sdiff (hs : IsUpperSet s) (ht : forall b in s, forall c in t, b <= c -> b in t) :
    IsUpperSet (s \ t) :=
fun _b _c hbc hb => ⟨hs hbc hb.1, fun hc => hb.2 ht _ hb.1 _ hc hbc⟩

@[to_dual]
/--
lemma `IsUpperSet.sdiff_of_isLowerSet` / 引理 `IsUpperSet.sdiff_of_isLowerSet`

English:
lemma IsUpperSet.sdiff_of_isLowerSet
  given: (hs : IsUpperSet s) (ht : IsLowerSet t)
  statement: IsUpperSet (s \ t)
  proof: hs.sdiff by aesop

@[to_dual]

中文:
引理 是上集.sdiff_of_isLowerSet
  条件: (hs : 是上集 s) (ht : 是下集 t)
  结论: 是上集 (s \ t)
  证明: hs.sdiff by aesop

@[to_dual]

Depends on / 依赖: hs.sdiff
-/
lemma IsUpperSet.sdiff_of_isLowerSet (hs : IsUpperSet s) (ht : IsLowerSet t) : IsUpperSet (s \ t) :=
hs.sdiff by aesop

@[to_dual]
/--
lemma `IsUpperSet.erase` / 引理 `IsUpperSet.erase`

English:
lemma IsUpperSet.erase
  given: (hs : IsUpperSet s) (has : forall b in s, b <= a -> b = a)
  statement: IsUpperSet (s \ {a})
  proof: hs.sdiff by simpa using has

中文:
引理 是上集.erase
  条件: (hs : 是上集 s) (has : 对任意 b in s, b <= a -> b = a)
  结论: 是上集 (s \ {a})
  证明: hs.sdiff by simpa using has

Depends on / 依赖: hs.sdiff
-/
lemma IsUpperSet.erase (hs : IsUpperSet s) (has : forall b in s, b <= a -> b = a) : IsUpperSet (s \ {a}) :=
hs.sdiff by simpa using has

end LE

section Preorder

variable [Preorder α] [Preorder β] {s : Set α} {p : α -> Prop} (a : α)

/--
theorem `isUpperSet_Ici` / 定理 `isUpperSet_Ici`

English:
theorem isUpperSet_Ici
  statement: IsUpperSet (Ici a)
  proof: fun _ _ => ge_trans

中文:
定理 isUpperSet_Ici
  结论: 是上集 (左闭右无界区间 a)
  证明: fun _ _ => ge_trans
-/
@[to_dual] theorem isUpperSet_Ici : IsUpperSet (Ici a) := fun _ _ => ge_trans
/--
theorem `isUpperSet_Ioi` / 定理 `isUpperSet_Ioi`

English:
theorem isUpperSet_Ioi
  statement: IsUpperSet (Ioi a)
  proof: fun _ _ => flip lt_of_lt_of_le

@[to_dual]

中文:
定理 isUpperSet_Ioi
  结论: 是上集 (左开右无界区间 a)
  证明: fun _ _ => flip lt_of_lt_of_le

@[to_dual]
-/
@[to_dual] theorem isUpperSet_Ioi : IsUpperSet (Ioi a) := fun _ _ => flip lt_of_lt_of_le

@[to_dual]
/--
theorem `isUpperSet_iff_Ici_subset` / 定理 `isUpperSet_iff_Ici_subset`

English:
theorem isUpperSet_iff_Ici_subset
  statement: IsUpperSet s ↔ forall ⦃a⦄, a in s -> Ici a subseteq s
  proof: by
  simp [IsUpperSet, subset_def, @forall_comm (_ in s)]

@[to_dual] alias ⟨IsUpperSet.Ici_subset, _⟩ := isUpperSet_iff_Ici_subset

@[to_dual]

中文:
定理 isUpperSet_iff_Ici_subset
  结论: 是上集 s ↔ 对任意 ⦃a⦄, a in s -> 左闭右无界区间 a subseteq s
  证明: by
  simp [IsUpperSet, subset_def, @forall_comm (_ in s)]

@[to_dual] alias ⟨IsUpperSet.Ici_subset, _⟩ := isUpperSet_iff_Ici_subset

@[to_dual]

Depends on / 依赖: IsUpperSet, forall_comm, subset_def
-/
theorem isUpperSet_iff_Ici_subset : IsUpperSet s ↔ forall ⦃a⦄, a in s -> Ici a subseteq s := by
  simp [IsUpperSet, subset_def, @forall_comm (_ in s)]

@[to_dual] alias ⟨IsUpperSet.Ici_subset, _⟩ := isUpperSet_iff_Ici_subset

@[to_dual]
/--
theorem `IsUpperSet.Ioi_subset` / 定理 `IsUpperSet.Ioi_subset`

English:
theorem IsUpperSet.Ioi_subset
  given: (h : IsUpperSet s) ⦃a⦄ (ha : a in s)
  statement: Ioi a subseteq s
  proof: Ioi_subset_Ici_self.trans h.Ici_subset ha

中文:
定理 是上集.Ioi_subset
  条件: (h : 是上集 s) ⦃a⦄ (ha : a in s)
  结论: 左开右无界区间 a subseteq s
  证明: Ioi_subset_Ici_self.trans h.Ici_subset ha

Depends on / 依赖: Ici_subset, Ioi_subset_Ici_self, Ioi_subset_Ici_self.trans, h.Ici_subset
-/
theorem IsUpperSet.Ioi_subset (h : IsUpperSet s) ⦃a⦄ (ha : a in s) : Ioi a subseteq s :=
Ioi_subset_Ici_self.trans h.Ici_subset ha

/--
theorem `IsUpperSet.ordConnected` / 定理 `IsUpperSet.ordConnected`

English:
theorem IsUpperSet.ordConnected
  given: (h : IsUpperSet s)
  statement: s.OrdConnected
  proof: ⟨fun _ ha _ _ => Icc_subset_Ici_self.trans h.Ici_subset ha⟩

中文:
定理 是上集.ordConnected
  条件: (h : 是上集 s)
  结论: s.序连通
  证明: ⟨fun _ ha _ _ => Icc_subset_Ici_self.trans h.Ici_subset ha⟩

Depends on / 依赖: Icc_subset_Ici_self, Icc_subset_Ici_self.trans, Ici_subset, h.Ici_subset
-/
theorem IsUpperSet.ordConnected (h : IsUpperSet s) : s.OrdConnected :=
⟨fun _ ha _ _ => Icc_subset_Ici_self.trans h.Ici_subset ha⟩

-- `to_dual` cannot yet reorder arguments of arguments
@[to_dual existing]
/--
theorem `IsLowerSet.ordConnected` / 定理 `IsLowerSet.ordConnected`

English:
theorem IsLowerSet.ordConnected
  given: (h : IsLowerSet s)
  statement: s.OrdConnected
  proof: ⟨fun _ _ _ hb => Icc_subset_Iic_self.trans h.Iic_subset hb⟩

@[to_dual]

中文:
定理 是下集.ordConnected
  条件: (h : 是下集 s)
  结论: s.序连通
  证明: ⟨fun _ _ _ hb => Icc_subset_Iic_self.trans h.Iic_subset hb⟩

@[to_dual]

Depends on / 依赖: Icc_subset_Iic_self, Icc_subset_Iic_self.trans, Iic_subset, h.Iic_subset
-/
theorem IsLowerSet.ordConnected (h : IsLowerSet s) : s.OrdConnected :=
⟨fun _ _ _ hb => Icc_subset_Iic_self.trans h.Iic_subset hb⟩

@[to_dual]
/--
theorem `IsUpperSet.preimage` / 定理 `IsUpperSet.preimage`

English:
theorem IsUpperSet.preimage
  given: (hs : IsUpperSet s) {f : β -> α} (hf : Monotone f)
  proof: fun _ _ h => hs hf h

@[to_dual]

中文:
定理 是上集.原像
  条件: (hs : 是上集 s) {f : β -> α} (hf : 递增 f)
  证明: fun _ _ h => hs hf h

@[to_dual]
-/
theorem IsUpperSet.preimage (hs : IsUpperSet s) {f : β -> α} (hf : Monotone f) :
IsUpperSet (f ⁻¹' s : Set β) := fun _ _ h => hs hf h

@[to_dual]
/--
theorem `IsUpperSet.image` / 定理 `IsUpperSet.image`

English:
theorem IsUpperSet.image
  given: (hs : IsUpperSet s) (f : α ≃o β)
  statement: IsUpperSet (f '' s : Set β)
  proof: by
  change IsUpperSet ((f : α ≃ β) '' s)
  rw [Equiv.image_eq_preimage_symm]
  exact hs.preimage f.symm.monotone

@[to_dual]

中文:
定理 是上集.像
  条件: (hs : 是上集 s) (f : α ≃o β)
  结论: 是上集 (f '' s : 集合 β)
  证明: by
  change IsUpperSet ((f : α ≃ β) '' s)
  rw [Equiv.image_eq_preimage_symm]
  exact hs.preimage f.symm.monotone

@[to_dual]

Depends on / 依赖: Equiv.image_eq_preimage_symm, IsUpperSet, f.symm.monotone, hs.preimage, image_eq_preimage_symm, monotone, preimage
-/
theorem IsUpperSet.image (hs : IsUpperSet s) (f : α ≃o β) : IsUpperSet (f '' s : Set β) := by
  change IsUpperSet ((f : α ≃ β) '' s)
  rw [Equiv.image_eq_preimage_symm]
  exact hs.preimage f.symm.monotone

@[to_dual]
/--
theorem `OrderEmbedding.image_Ici` / 定理 `OrderEmbedding.image_Ici`

English:
theorem OrderEmbedding.image_Ici
  given: (e : α ↪o β) (he : IsUpperSet (range e)) (a : α)
  proof: by
  rw [← e.preimage_Ici]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 he.Ici_subset (mem_range_self _)]

@[to_dual]

中文:
定理 OrderEmbedding.image_Ici
  条件: (e : α ↪o β) (he : 是上集 (range e)) (a : α)
  证明: by
  rw [← e.preimage_Ici]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 he.Ici_subset (mem_range_self _)]

@[to_dual]

Depends on / 依赖: Ici_subset, e.preimage_Ici, he.Ici_subset, image_preimage_eq_inter_range, inter_eq_left, mem_range_self, preimage_Ici
-/
theorem OrderEmbedding.image_Ici (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) :
    e '' Ici a = Ici (e a) := by
  rw [← e.preimage_Ici]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 he.Ici_subset (mem_range_self _)]

@[to_dual]
/--
theorem `OrderEmbedding.image_Ioi` / 定理 `OrderEmbedding.image_Ioi`

English:
theorem OrderEmbedding.image_Ioi
  given: (e : α ↪o β) (he : IsUpperSet (range e)) (a : α)
  proof: by
  rw [← e.preimage_Ioi]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 he.Ioi_subset (mem_range_self _)]

@[simp]

中文:
定理 OrderEmbedding.image_Ioi
  条件: (e : α ↪o β) (he : 是上集 (range e)) (a : α)
  证明: by
  rw [← e.preimage_Ioi]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 he.Ioi_subset (mem_range_self _)]

@[simp]

Depends on / 依赖: Ioi_subset, e.preimage_Ioi, he.Ioi_subset, image_preimage_eq_inter_range, inter_eq_left, mem_range_self, preimage_Ioi
-/
theorem OrderEmbedding.image_Ioi (e : α ↪o β) (he : IsUpperSet (range e)) (a : α) :
    e '' Ioi a = Ioi (e a) := by
  rw [← e.preimage_Ioi]; rw [image_preimage_eq_inter_range]; rw [inter_eq_left.2 he.Ioi_subset (mem_range_self _)]

@[simp]
/--
theorem `Set.monotone_mem` / 定理 `Set.monotone_mem`

English:
theorem Set.monotone_mem
  statement: Monotone (· in s) ↔ IsUpperSet s
  proof: Iff.rfl

@[simp]

中文:
定理 集合.monotone_mem
  结论: 递增 (· in s) ↔ 是上集 s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem Set.monotone_mem : Monotone (· in s) ↔ IsUpperSet s :=
  Iff.rfl

@[simp]
/--
theorem `Set.antitone_mem` / 定理 `Set.antitone_mem`

English:
theorem Set.antitone_mem
  statement: Antitone (· in s) ↔ IsLowerSet s
  proof: forall_comm

@[simp]

中文:
定理 集合.antitone_mem
  结论: 递减 (· in s) ↔ 是下集 s
  证明: forall_comm

@[simp]

Depends on / 依赖: forall_comm
-/
theorem Set.antitone_mem : Antitone (· in s) ↔ IsLowerSet s :=
  forall_comm

@[simp]
/--
theorem `isUpperSet_setOfPred` / 定理 `isUpperSet_setOfPred`

English:
theorem isUpperSet_setOfPred
  statement: IsUpperSet { a | p a } ↔ Monotone p
  proof: Iff.rfl

@[deprecated (since := "2026-07-09")] alias isUpperSet_setOf := isUpperSet_setOfPred

@[simp]

中文:
定理 isUpperSet_setOfPred
  结论: 是上集 { a | p a } ↔ 递增 p
  证明: Iff.rfl

@[deprecated (since := "2026-07-09")] alias isUpperSet_setOf := isUpperSet_setOfPred

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem isUpperSet_setOfPred : IsUpperSet { a | p a } ↔ Monotone p :=
  Iff.rfl

@[deprecated (since := "2026-07-09")] alias isUpperSet_setOf := isUpperSet_setOfPred

@[simp]
/--
theorem `isLowerSet_setOfPred` / 定理 `isLowerSet_setOfPred`

English:
theorem isLowerSet_setOfPred
  statement: IsLowerSet { a | p a } ↔ Antitone p
  proof: forall_comm

@[deprecated (since := "2026-07-09")] alias isLowerSet_setOf := isLowerSet_setOfPred

@[to_dual]

中文:
定理 isLowerSet_setOfPred
  结论: 是下集 { a | p a } ↔ 递减 p
  证明: forall_comm

@[deprecated (since := "2026-07-09")] alias isLowerSet_setOf := isLowerSet_setOfPred

@[to_dual]

Depends on / 依赖: forall_comm
-/
theorem isLowerSet_setOfPred : IsLowerSet { a | p a } ↔ Antitone p :=
  forall_comm

@[deprecated (since := "2026-07-09")] alias isLowerSet_setOf := isLowerSet_setOfPred

@[to_dual]
/--
lemma `IsUpperSet.upperBounds_subset` / 引理 `IsUpperSet.upperBounds_subset`

English:
lemma IsUpperSet.upperBounds_subset
  given: (hs : IsUpperSet s)
  statement: s.Nonempty -> upperBounds s subseteq s
  proof: fun ⟨_a, ha⟩ _b hb => hs (hb ha) ha

中文:
引理 是上集.upperBounds_subset
  条件: (hs : 是上集 s)
  结论: s.非空 -> upperBounds s subseteq s
  证明: fun ⟨_a, ha⟩ _b hb => hs (hb ha) ha
-/
lemma IsUpperSet.upperBounds_subset (hs : IsUpperSet s) : s.Nonempty -> upperBounds s subseteq s :=
  fun ⟨_a, ha⟩ _b hb => hs (hb ha) ha

section OrderTop

variable [OrderTop α]

@[to_dual]
/--
theorem `IsLowerSet.top_mem` / 定理 `IsLowerSet.top_mem`

English:
theorem IsLowerSet.top_mem
  given: (hs : IsLowerSet s)
  statement: ⊤ in s ↔ s = univ
  proof: ⟨fun h => eq_univ_of_forall fun _ => hs le_top h, fun h => h.symm ▸ mem_univ _⟩

@[to_dual]

中文:
定理 是下集.top_mem
  条件: (hs : 是下集 s)
  结论: ⊤ in s ↔ s = univ
  证明: ⟨fun h => eq_univ_of_forall fun _ => hs le_top h, fun h => h.symm ▸ mem_univ _⟩

@[to_dual]

Depends on / 依赖: eq_univ_of_forall, h.symm, le_top, mem_univ
-/
theorem IsLowerSet.top_mem (hs : IsLowerSet s) : ⊤ in s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun _ => hs le_top h, fun h => h.symm ▸ mem_univ _⟩

@[to_dual]
/--
theorem `IsUpperSet.top_mem` / 定理 `IsUpperSet.top_mem`

English:
theorem IsUpperSet.top_mem
  given: (hs : IsUpperSet s)
  statement: ⊤ in s ↔ s.Nonempty
  proof: ⟨fun h => ⟨_, h⟩, fun ⟨_a, ha⟩ => hs le_top ha⟩

@[to_dual]

中文:
定理 是上集.top_mem
  条件: (hs : 是上集 s)
  结论: ⊤ in s ↔ s.非空
  证明: ⟨fun h => ⟨_, h⟩, fun ⟨_a, ha⟩ => hs le_top ha⟩

@[to_dual]

Depends on / 依赖: le_top
-/
theorem IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ in s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨_a, ha⟩ => hs le_top ha⟩

@[to_dual]
/--
theorem `IsUpperSet.top_notMem` / 定理 `IsUpperSet.top_notMem`

English:
theorem IsUpperSet.top_notMem
  given: (hs : IsUpperSet s)
  statement: ⊤ ∉ s ↔ s = ∅
  proof: hs.top_mem.not.trans not_nonempty_iff_eq_empty

中文:
定理 是上集.top_notMem
  条件: (hs : 是上集 s)
  结论: ⊤ ∉ s ↔ s = ∅
  证明: hs.top_mem.not.trans not_nonempty_iff_eq_empty

Depends on / 依赖: hs.top_mem.not.trans, not_nonempty_iff_eq_empty, top_mem
-/
theorem IsUpperSet.top_notMem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅ :=
  hs.top_mem.not.trans not_nonempty_iff_eq_empty

end OrderTop

section NoMaxOrder

variable [NoMaxOrder α]

@[to_dual]
/--
theorem `IsUpperSet.not_bddAbove` / 定理 `IsUpperSet.not_bddAbove`

English:
theorem IsUpperSet.not_bddAbove
  given: (hs : IsUpperSet s)
  statement: s.Nonempty -> ¬BddAbove s
  proof: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_ge (hb <| hs ((hb ha).trans hc.le) ha)

@[to_dual]

中文:
定理 是上集.not_bddAbove
  条件: (hs : 是上集 s)
  结论: s.非空 -> ¬BddAbove s
  证明: by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_ge (hb <| hs ((hb ha).trans hc.le) ha)

@[to_dual]

Depends on / 依赖: exists_gt, hc.le, hc.not_ge, not_ge
-/
theorem IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s.Nonempty -> ¬BddAbove s := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_ge (hb <| hs ((hb ha).trans hc.le) ha)

@[to_dual]
/--
theorem `not_bddAbove_Ici` / 定理 `not_bddAbove_Ici`

English:
theorem not_bddAbove_Ici
  statement: ¬BddAbove (Ici a)
  proof: (isUpperSet_Ici _).not_bddAbove nonempty_Ici

@[to_dual]

中文:
定理 not_bddAbove_Ici
  结论: ¬BddAbove (左闭右无界区间 a)
  证明: (isUpperSet_Ici _).not_bddAbove nonempty_Ici

@[to_dual]

Depends on / 依赖: isUpperSet_Ici, nonempty_Ici, not_bddAbove
-/
theorem not_bddAbove_Ici : ¬BddAbove (Ici a) :=
  (isUpperSet_Ici _).not_bddAbove nonempty_Ici

@[to_dual]
/--
theorem `not_bddAbove_Ioi` / 定理 `not_bddAbove_Ioi`

English:
theorem not_bddAbove_Ioi
  statement: ¬BddAbove (Ioi a)
  proof: (isUpperSet_Ioi _).not_bddAbove nonempty_Ioi

中文:
定理 not_bddAbove_Ioi
  结论: ¬BddAbove (左开右无界区间 a)
  证明: (isUpperSet_Ioi _).not_bddAbove nonempty_Ioi

Depends on / 依赖: isUpperSet_Ioi, nonempty_Ioi, not_bddAbove
-/
theorem not_bddAbove_Ioi : ¬BddAbove (Ioi a) :=
  (isUpperSet_Ioi _).not_bddAbove nonempty_Ioi

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α}

@[to_dual]
/--
theorem `isUpperSet_iff_forall_lt` / 定理 `isUpperSet_iff_forall_lt`

English:
theorem isUpperSet_iff_forall_lt
  statement: IsUpperSet s ↔ forall ⦃a b : α⦄, a < b -> a in s -> b in s
  proof: forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]

@[to_dual]

中文:
定理 isUpperSet_iff_对任意_lt
  结论: 是上集 s ↔ 对任意 ⦃a b : α⦄, a < b -> a in s -> b in s
  证明: forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]

@[to_dual]

Depends on / 依赖: forall_and, forall_congr, le_iff_eq_or_lt, or_imp
-/
theorem isUpperSet_iff_forall_lt : IsUpperSet s ↔ forall ⦃a b : α⦄, a < b -> a in s -> b in s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]

@[to_dual]
/--
theorem `isUpperSet_iff_Ioi_subset` / 定理 `isUpperSet_iff_Ioi_subset`

English:
theorem isUpperSet_iff_Ioi_subset
  statement: IsUpperSet s ↔ forall ⦃a⦄, a in s -> Ioi a subseteq s
  proof: by
  simp [isUpperSet_iff_forall_lt, subset_def, @forall_comm (_ in s)]

中文:
定理 isUpperSet_iff_Ioi_subset
  结论: 是上集 s ↔ 对任意 ⦃a⦄, a in s -> 左开右无界区间 a subseteq s
  证明: by
  simp [isUpperSet_iff_forall_lt, subset_def, @forall_comm (_ in s)]

Depends on / 依赖: forall_comm, isUpperSet_iff_forall_lt, subset_def
-/
theorem isUpperSet_iff_Ioi_subset : IsUpperSet s ↔ forall ⦃a⦄, a in s -> Ioi a subseteq s := by
  simp [isUpperSet_iff_forall_lt, subset_def, @forall_comm (_ in s)]

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s t : Set α}

@[to_dual]
/--
theorem `IsUpperSet.total` / 定理 `IsUpperSet.total`

English:
theorem IsUpperSet.total
  given: (hs : IsUpperSet s) (ht : IsUpperSet t)
  statement: s subseteq t ∨ t subseteq s
  proof: by
  grind [isUpperSet_iff_forall_lt]

@[to_dual]

中文:
定理 是上集.total
  条件: (hs : 是上集 s) (ht : 是上集 t)
  结论: s subseteq t ∨ t subseteq s
  证明: by
  grind [isUpperSet_iff_forall_lt]

@[to_dual]

Depends on / 依赖: isUpperSet_iff_forall_lt
-/
theorem IsUpperSet.total (hs : IsUpperSet s) (ht : IsUpperSet t) : s subseteq t ∨ t subseteq s := by
  grind [isUpperSet_iff_forall_lt]

@[to_dual]
/--
theorem `IsUpperSet.eq_empty_or_Ici` / 定理 `IsUpperSet.eq_empty_or_Ici`

English:
theorem IsUpperSet.eq_empty_or_Ici
  given: [WellFoundedLT α] (h : IsUpperSet s)
  proof: by
  refine or_iff_not_imp_left.2 fun ha => ?_
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 ha
  exact ⟨_, ext fun b => ⟨wellFounded_lt.min_le, (h · <| wellFounded_lt.min_mem _ ⟨a, ha⟩)⟩⟩

@[to_dual]

中文:
定理 是上集.eq_empty_or_Ici
  条件: [WellFoundedLT α] (h : 是上集 s)
  证明: by
  refine or_iff_not_imp_left.2 fun ha => ?_
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 ha
  exact ⟨_, ext fun b => ⟨wellFounded_lt.min_le, (h · <| wellFounded_lt.min_mem _ ⟨a, ha⟩)⟩⟩

@[to_dual]

Depends on / 依赖: Set.nonempty_iff_ne_empty, min_le, min_mem, nonempty_iff_ne_empty, or_iff_not_imp_left, wellFounded_lt, wellFounded_lt.min_le, wellFounded_lt.min_mem
-/
theorem IsUpperSet.eq_empty_or_Ici [WellFoundedLT α] (h : IsUpperSet s) :
    s = ∅ ∨ exists a, s = Ici a := by
  refine or_iff_not_imp_left.2 fun ha => ?_
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 ha
  exact ⟨_, ext fun b => ⟨wellFounded_lt.min_le, (h · <| wellFounded_lt.min_mem _ ⟨a, ha⟩)⟩⟩

@[to_dual]
/--
theorem `IsLowerSet.eq_univ_or_Iio` / 定理 `IsLowerSet.eq_univ_or_Iio`

English:
theorem IsLowerSet.eq_univ_or_Iio
  given: [WellFoundedLT α] (h : IsLowerSet s)
  proof: by
  simp_rw [← @compl_inj_iff _ s]
  simpa using h.compl.eq_empty_or_Ici

中文:
定理 是下集.eq_univ_or_Iio
  条件: [WellFoundedLT α] (h : 是下集 s)
  证明: by
  simp_rw [← @compl_inj_iff _ s]
  simpa using h.compl.eq_empty_or_Ici

Depends on / 依赖: compl_inj_iff, eq_empty_or_Ici, h.compl.eq_empty_or_Ici, simp_rw
-/
theorem IsLowerSet.eq_univ_or_Iio [WellFoundedLT α] (h : IsLowerSet s) :
    s = univ ∨ exists a, s = Iio a := by
  simp_rw [← @compl_inj_iff _ s]
  simpa using h.compl.eq_empty_or_Ici

end LinearOrder
