/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.GameAdd
public import Mathlib.SetTheory.ZFC.Cardinal
public import Mathlib.SetTheory.ZFC.Rank

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`.

## Definitions

- `ZFSet.IsTransitive` means that every element of a set is a subset.
- `ZFSet.IsOrdinal` means that the set is transitive and well-ordered under `∈`. We show multiple
  equivalences to this definition.
- `Ordinal.toZFSet` converts Lean's type-theoretic ordinals into ZFC ordinals. We prove that these
  two notions are order-isomorphic.
-/

@[expose] public section

universe u

variable {x y z w : ZFSet.{u}}

open Set

namespace ZFSet

/-! ### Transitive sets -/

/--
Definition of `IsTransitive` / `IsTransitive` 的定义

English:
definition IsTransitive
  signature: (x : ZFSet)
  body: forall y in x, y subseteq x

@[simp]

中文:
定义 IsTransitive
  签名: (x : ZFSet)
  定义体: forall y in x, y subseteq x

@[simp]

Depends on / 依赖: subseteq
-/
def IsTransitive (x : ZFSet) : Prop :=
  forall y in x, y subseteq x

@[simp]
/--
theorem `isTransitive_empty` / 定理 `isTransitive_empty`

English:
theorem isTransitive_empty
  statement: IsTransitive ∅
  proof: fun y hy => (notMem_empty y hy).elim

中文:
定理 isTransitive_empty
  结论: IsTransitive ∅
  证明: fun y hy => (notMem_empty y hy).elim

Depends on / 依赖: notMem_empty
-/
theorem isTransitive_empty : IsTransitive ∅ := fun y hy => (notMem_empty y hy).elim

/--
theorem `IsTransitive.subset_of_mem` / 定理 `IsTransitive.subset_of_mem`

English:
theorem IsTransitive.subset_of_mem
  given: (h : x.IsTransitive)
  statement: y in x -> y subseteq x
  proof: h y

中文:
定理 IsTransitive.subset_of_mem
  条件: (h : x.IsTransitive)
  结论: y in x -> y subseteq x
  证明: h y
-/
theorem IsTransitive.subset_of_mem (h : x.IsTransitive) : y in x -> y subseteq x := h y

/--
theorem `isTransitive_iff_mem_trans` / 定理 `isTransitive_iff_mem_trans`

English:
theorem isTransitive_iff_mem_trans
  statement: z.IsTransitive ↔ forall {x y : ZFSet}, x in y -> y in z -> x in z
  proof: ⟨fun h _ _ hx hy => h.subset_of_mem hy hx, fun H _ hx _ hy => H hy hx⟩

alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans

中文:
定理 isTransitive_iff_mem_trans
  结论: z.IsTransitive ↔ 对任意 {x y : ZFSet}, x in y -> y in z -> x in z
  证明: ⟨fun h _ _ hx hy => h.subset_of_mem hy hx, fun H _ hx _ hy => H hy hx⟩

alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans

Depends on / 依赖: h.subset_of_mem, subset_of_mem
-/
theorem isTransitive_iff_mem_trans : z.IsTransitive ↔ forall {x y : ZFSet}, x in y -> y in z -> x in z :=
  ⟨fun h _ _ hx hy => h.subset_of_mem hy hx, fun H _ hx _ hy => H hy hx⟩

alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans

/--
theorem `IsTransitive.inter` / 定理 `IsTransitive.inter`

English:
theorem IsTransitive.inter
  given: (hx : x.IsTransitive) (hy : y.IsTransitive)
  proof: fun z hz w hw => by
  rw [mem_inter] at hz ⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩

中文:
定理 IsTransitive.inter
  条件: (hx : x.IsTransitive) (hy : y.IsTransitive)
  证明: fun z hz w hw => by
  rw [mem_inter] at hz ⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩
-/
protected theorem IsTransitive.inter (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x inter y).IsTransitive := fun z hz w hw => by
  rw [mem_inter] at hz ⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩

/--
theorem `IsTransitive.sUnion` / 定理 `IsTransitive.sUnion`

English:
theorem IsTransitive.sUnion
  given: (h : x.IsTransitive)
  proof: fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)

中文:
定理 IsTransitive.sUnion
  条件: (h : x.IsTransitive)
  证明: fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)
-/
protected theorem IsTransitive.sUnion (h : x.IsTransitive) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)

/--
theorem `IsTransitive.sUnion'` / 定理 `IsTransitive.sUnion'`

English:
theorem IsTransitive.sUnion'
  given: (H : forall y in x, IsTransitive y)
  proof: fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw

中文:
定理 IsTransitive.sUnion'
  条件: (H : 对任意 y in x, IsTransitive y)
  证明: fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw

Depends on / 依赖: mem_sUnion, mem_sUnion_of_mem, mem_trans
-/
theorem IsTransitive.sUnion' (H : forall y in x, IsTransitive y) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw

/--
theorem `IsTransitive.iUnion` / 定理 `IsTransitive.iUnion`

English:
theorem IsTransitive.iUnion
  statement: {α : Type*} [Small.{u} α] {f : α -> ZFSet.{u}}
  proof: sUnion' (by simpa)

中文:
定理 IsTransitive.iUnion
  结论: {α : 类型} [Small.{u} α] {f : α -> ZFSet.{u}}
  证明: sUnion' (by simpa)
-/
protected theorem IsTransitive.iUnion {α : Type*} [Small.{u} α] {f : α -> ZFSet.{u}}
    (hf : forall i, (f i).IsTransitive) : (⋃ i, f i).IsTransitive :=
  sUnion' (by simpa)

/--
theorem `IsTransitive.union` / 定理 `IsTransitive.union`

English:
theorem IsTransitive.union
  given: (hx : x.IsTransitive) (hy : y.IsTransitive)
  proof: by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion'
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'

中文:
定理 IsTransitive.union
  条件: (hx : x.IsTransitive) (hy : y.IsTransitive)
  证明: by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion'
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'
-/
protected theorem IsTransitive.union (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x union y).IsTransitive := by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion'
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'

/--
theorem `IsTransitive.powerset` / 定理 `IsTransitive.powerset`

English:
theorem IsTransitive.powerset
  given: (h : x.IsTransitive)
  statement: (powerset x).IsTransitive
  proof: fun y hy z hz => by
  rw [mem_powerset] at hy ⊢
  exact h.subset_of_mem (hy hz)

中文:
定理 IsTransitive.powerset
  条件: (h : x.IsTransitive)
  结论: (powerset x).IsTransitive
  证明: fun y hy z hz => by
  rw [mem_powerset] at hy ⊢
  exact h.subset_of_mem (hy hz)
-/
protected theorem IsTransitive.powerset (h : x.IsTransitive) : (powerset x).IsTransitive :=
  fun y hy z hz => by
  rw [mem_powerset] at hy ⊢
  exact h.subset_of_mem (hy hz)

/--
theorem `isTransitive_iff_sUnion_subset` / 定理 `isTransitive_iff_sUnion_subset`

English:
theorem isTransitive_iff_sUnion_subset
  statement: x.IsTransitive ↔ (⋃₀ x : ZFSet) subseteq x
  proof: by
  constructor <;>
  intro h y hy
  · obtain ⟨z, hz, hz'⟩ := mem_sUnion.1 hy
    exact h.mem_trans hz' hz
· exact fun z hz => h mem_sUnion_of_mem hz hy

alias ⟨IsTransitive.sUnion_subset, _⟩ := isTransitive_iff_sUnion_subset

中文:
定理 isTransitive_iff_sUnion_subset
  结论: x.IsTransitive ↔ (⋃₀ x : ZFSet) subseteq x
  证明: by
  constructor <;>
  intro h y hy
  · obtain ⟨z, hz, hz'⟩ := mem_sUnion.1 hy
    exact h.mem_trans hz' hz
· exact fun z hz => h mem_sUnion_of_mem hz hy

alias ⟨IsTransitive.sUnion_subset, _⟩ := isTransitive_iff_sUnion_subset

Depends on / 依赖: h.mem_trans, mem_sUnion, mem_sUnion_of_mem, mem_trans
-/
theorem isTransitive_iff_sUnion_subset : x.IsTransitive ↔ (⋃₀ x : ZFSet) subseteq x := by
  constructor <;>
  intro h y hy
  · obtain ⟨z, hz, hz'⟩ := mem_sUnion.1 hy
    exact h.mem_trans hz' hz
· exact fun z hz => h mem_sUnion_of_mem hz hy

alias ⟨IsTransitive.sUnion_subset, _⟩ := isTransitive_iff_sUnion_subset

/--
theorem `isTransitive_iff_subset_powerset` / 定理 `isTransitive_iff_subset_powerset`

English:
theorem isTransitive_iff_subset_powerset
  statement: x.IsTransitive ↔ x subseteq powerset x
  proof: ⟨fun h _ hy => mem_powerset.2 h.subset_of_mem hy, fun H _ hy _ hz => mem_powerset.1 (H hy) hz⟩

alias ⟨IsTransitive.subset_powerset, _⟩ := isTransitive_iff_subset_powerset

中文:
定理 isTransitive_iff_subset_powerset
  结论: x.IsTransitive ↔ x subseteq powerset x
  证明: ⟨fun h _ hy => mem_powerset.2 h.subset_of_mem hy, fun H _ hy _ hz => mem_powerset.1 (H hy) hz⟩

alias ⟨IsTransitive.subset_powerset, _⟩ := isTransitive_iff_subset_powerset

Depends on / 依赖: h.subset_of_mem, mem_powerset, subset_of_mem
-/
theorem isTransitive_iff_subset_powerset : x.IsTransitive ↔ x subseteq powerset x :=
⟨fun h _ hy => mem_powerset.2 h.subset_of_mem hy, fun H _ hy _ hz => mem_powerset.1 (H hy) hz⟩

alias ⟨IsTransitive.subset_powerset, _⟩ := isTransitive_iff_subset_powerset

/-! ### Ordinals -/

/--
Definition of `IsOrdinal` / `IsOrdinal` 的定义

English:
structure IsOrdinal
  parameters: (x : ZFSet)
  axioms and operations (2):
    - isTransitive : x.IsTransitive
    - mem_trans'({y z w : ZFSet}) : y in z -> z in w -> w in x -> y in w

中文:
结构 IsOrdinal
  参数: (x : ZFSet)
  公理与运算 (2 个):
    - isTransitive : x.IsTransitive
    - mem_trans'({y z w : ZFSet}) : y in z -> z in w -> w in x -> y in w
-/
structure IsOrdinal (x : ZFSet) : Prop where
  /-- An ordinal is a transitive set. -/
  isTransitive : x.IsTransitive
  /-- The membership operation within an ordinal is transitive. -/
  mem_trans' {y z w : ZFSet} : y in z -> z in w -> w in x -> y in w

namespace IsOrdinal

/--
theorem `subset_of_mem` / 定理 `subset_of_mem`

English:
theorem subset_of_mem
  given: (h : x.IsOrdinal)
  statement: y in x -> y subseteq x
  proof: h.isTransitive.subset_of_mem

中文:
定理 subset_of_mem
  条件: (h : x.IsOrdinal)
  结论: y in x -> y subseteq x
  证明: h.isTransitive.subset_of_mem

Depends on / 依赖: h.isTransitive.subset_of_mem, isTransitive, subset_of_mem
-/
theorem subset_of_mem (h : x.IsOrdinal) : y in x -> y subseteq x :=
  h.isTransitive.subset_of_mem

/--
theorem `mem_trans` / 定理 `mem_trans`

English:
theorem mem_trans
  given: (h : z.IsOrdinal)
  statement: x in y -> y in z -> x in z
  proof: h.isTransitive.mem_trans

中文:
定理 mem_trans
  条件: (h : z.IsOrdinal)
  结论: x in y -> y in z -> x in z
  证明: h.isTransitive.mem_trans

Depends on / 依赖: h.isTransitive.mem_trans, isTransitive, mem_trans
-/
theorem mem_trans (h : z.IsOrdinal) : x in y -> y in z -> x in z :=
  h.isTransitive.mem_trans

/--
theorem `isTrans` / 定理 `isTrans`

English:
theorem isTrans
  given: (h : x.IsOrdinal)
  statement: IsTrans _ (Subrel (· in ·) (· in x))
  proof: ⟨fun _ _ c hab hbc => h.mem_trans' hab hbc c.2⟩

中文:
定理 isTrans
  条件: (h : x.IsOrdinal)
  结论: IsTrans _ (Subrel (· in ·) (· in x))
  证明: ⟨fun _ _ c hab hbc => h.mem_trans' hab hbc c.2⟩
-/
protected theorem isTrans (h : x.IsOrdinal) : IsTrans _ (Subrel (· in ·) (· in x)) :=
  ⟨fun _ _ c hab hbc => h.mem_trans' hab hbc c.2⟩

/--
theorem `_root_.ZFSet.isOrdinal_iff_isTrans` / 定理 `_root_.ZFSet.isOrdinal_iff_isTrans`

English:
theorem _root_.ZFSet.isOrdinal_iff_isTrans
  proof: ⟨h.isTransitive, h.isTrans⟩
  mpr := by
    rintro ⟨h₁, ⟨h₂⟩⟩
    refine ⟨h₁, fun {y z w} hyz hzw hwx => ?_⟩
    have hzx := h₁.mem_trans hzw hwx
    exact h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw

中文:
定理 _root_.ZFSet.isOrdinal_iff_isTrans
  证明: ⟨h.isTransitive, h.isTrans⟩
  mpr := by
    rintro ⟨h₁, ⟨h₂⟩⟩
    refine ⟨h₁, fun {y z w} hyz hzw hwx => ?_⟩
    have hzx := h₁.mem_trans hzw hwx
    exact h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw

Depends on / 依赖: h.isTrans, h.isTransitive, isTrans, isTransitive
-/
theorem _root_.ZFSet.isOrdinal_iff_isTrans :
    x.IsOrdinal ↔ x.IsTransitive ∧ IsTrans _ (Subrel (· in ·) (· in x)) where
  mp h := ⟨h.isTransitive, h.isTrans⟩
  mpr := by
    rintro ⟨h₁, ⟨h₂⟩⟩
    refine ⟨h₁, fun {y z w} hyz hzw hwx => ?_⟩
    have hzx := h₁.mem_trans hzw hwx
    exact h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw

/--
theorem `mem` / 定理 `mem`

English:
theorem mem
  given: (hx : x.IsOrdinal) (hy : y in x)
  statement: y.IsOrdinal
  proof: have := hx.isTrans
  let f : _ ↪r Subrel (· in ·) (· in x) := Subrel.inclusionEmbedding (· in ·) (hx.subset_of_mem hy)
  isOrdinal_iff_isTrans.2 ⟨fun _ hz _ ha => hx.mem_trans' ha hz hy, f.isTrans⟩

中文:
定理 mem
  条件: (hx : x.IsOrdinal) (hy : y in x)
  结论: y.IsOrdinal
  证明: have := hx.isTrans
  let f : _ ↪r Subrel (· in ·) (· in x) := Subrel.inclusionEmbedding (· in ·) (hx.subset_of_mem hy)
  isOrdinal_iff_isTrans.2 ⟨fun _ hz _ ha => hx.mem_trans' ha hz hy, f.isTrans⟩
-/
protected theorem mem (hx : x.IsOrdinal) (hy : y in x) : y.IsOrdinal :=
  have := hx.isTrans
  let f : _ ↪r Subrel (· in ·) (· in x) := Subrel.inclusionEmbedding (· in ·) (hx.subset_of_mem hy)
  isOrdinal_iff_isTrans.2 ⟨fun _ hz _ ha => hx.mem_trans' ha hz hy, f.isTrans⟩

/--
theorem `_root_.ZFSet.isOrdinal_iff_forall_mem_isTransitive` / 定理 `_root_.ZFSet.isOrdinal_iff_forall_mem_isTransitive`

English:
theorem _root_.ZFSet.isOrdinal_iff_forall_mem_isTransitive
  proof: ⟨h.isTransitive, fun _ hy => (h.mem hy).isTransitive⟩
  mpr := fun ⟨h₁, h₂⟩ => ⟨h₁, fun hyz hzw hwx => (h₂ _ hwx).mem_trans hyz hzw⟩

中文:
定理 _root_.ZFSet.isOrdinal_iff_forall_mem_isTransitive
  证明: ⟨h.isTransitive, fun _ hy => (h.mem hy).isTransitive⟩
  mpr := fun ⟨h₁, h₂⟩ => ⟨h₁, fun hyz hzw hwx => (h₂ _ hwx).mem_trans hyz hzw⟩

Depends on / 依赖: h.isTransitive, h.mem, isTransitive
-/
theorem _root_.ZFSet.isOrdinal_iff_forall_mem_isTransitive :
    x.IsOrdinal ↔ x.IsTransitive ∧ forall y in x, y.IsTransitive where
  mp h := ⟨h.isTransitive, fun _ hy => (h.mem hy).isTransitive⟩
  mpr := fun ⟨h₁, h₂⟩ => ⟨h₁, fun hyz hzw hwx => (h₂ _ hwx).mem_trans hyz hzw⟩

/--
theorem `_root_.ZFSet.isOrdinal_iff_forall_mem_isOrdinal` / 定理 `_root_.ZFSet.isOrdinal_iff_forall_mem_isOrdinal`

English:
theorem _root_.ZFSet.isOrdinal_iff_forall_mem_isOrdinal
  proof: ⟨h.isTransitive, fun _ => h.mem⟩
  mpr := fun ⟨h₁, h₂⟩ => isOrdinal_iff_forall_mem_isTransitive.2
    ⟨h₁, fun y hy => (h₂ y hy).isTransitive⟩

中文:
定理 _root_.ZFSet.isOrdinal_iff_forall_mem_isOrdinal
  证明: ⟨h.isTransitive, fun _ => h.mem⟩
  mpr := fun ⟨h₁, h₂⟩ => isOrdinal_iff_forall_mem_isTransitive.2
    ⟨h₁, fun y hy => (h₂ y hy).isTransitive⟩

Depends on / 依赖: h.isTransitive, h.mem, isTransitive
-/
theorem _root_.ZFSet.isOrdinal_iff_forall_mem_isOrdinal :
    x.IsOrdinal ↔ x.IsTransitive ∧ forall y in x, y.IsOrdinal where
  mp h := ⟨h.isTransitive, fun _ => h.mem⟩
  mpr := fun ⟨h₁, h₂⟩ => isOrdinal_iff_forall_mem_isTransitive.2
    ⟨h₁, fun y hy => (h₂ y hy).isTransitive⟩

/--
theorem `subset_iff_eq_or_mem` / 定理 `subset_iff_eq_or_mem`

English:
theorem subset_iff_eq_or_mem
  given: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  statement: x subseteq y ↔ x = y ∨ x in y
  proof: by
  constructor
  · revert hx hy
    refine Sym2.GameAdd.recursion mem_wf ?_ x y
    intro x y IH hx hy hxy
    by_cases hyx : y subseteq x
    · exact Or.inl (subset_antisymm hxy hyx)
    · obtain ⟨m, hm, hm'⟩ := mem_wf.has_min (y \ x) (Set.sdiff_nonempty.2 hyx)
      have hmy : m in y := by simp 

中文:
定理 subset_iff_eq_or_mem
  条件: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  结论: x subseteq y ↔ x = y ∨ x in y
  证明: by
  constructor
  · revert hx hy
    refine Sym2.GameAdd.recursion mem_wf ?_ x y
    intro x y IH hx hy hxy
    by_cases hyx : y subseteq x
    · exact Or.inl (subset_antisymm hxy hyx)
    · obtain ⟨m, hm, hm'⟩ := mem_wf.has_min (y \ x) (Set.sdiff_nonempty.2 hyx)
      have hmy : m in y := by simp 

Depends on / 依赖: GameAdd, Or.inl, Set.mem_sdiff, Set.sdiff_nonempty, SetLike, SetLike.mem_coe, Sym2.GameAdd.fst_snd, Sym2.GameAdd.recursion, fst_snd, has_min, hy.mem, hy.mem_trans, mem_coe, mem_sdiff, mem_trans, mem_wf, mem_wf.has_min, recursion, revert, sdiff_nonempty
-/
theorem subset_iff_eq_or_mem (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x subseteq y ↔ x = y ∨ x in y := by
  constructor
  · revert hx hy
    refine Sym2.GameAdd.recursion mem_wf ?_ x y
    intro x y IH hx hy hxy
    by_cases hyx : y subseteq x
    · exact Or.inl (subset_antisymm hxy hyx)
    · obtain ⟨m, hm, hm'⟩ := mem_wf.has_min (y \ x) (Set.sdiff_nonempty.2 hyx)
      have hmy : m in y := by simp only [Set.mem_sdiff, SetLike.mem_coe] at hm; exact hm.1
      have hmx : m subseteq x := by
        intro z hzm
        by_contra hzx
        exact hm' _ ⟨hy.mem_trans hzm hmy, hzx⟩ hzm
      obtain rfl | H := IH m x (Sym2.GameAdd.fst_snd hmy) (hy.mem hmy) hx hmx
      · exact Or.inr hmy
      · cases Set.notMem_of_mem_sdiff hm H
  · rintro (rfl | h)
    · rfl
    · exact hy.subset_of_mem h

alias ⟨eq_or_mem_of_subset, _⟩ := subset_iff_eq_or_mem

/--
theorem `mem_of_subset_of_mem` / 定理 `mem_of_subset_of_mem`

English:
theorem mem_of_subset_of_mem
  given: (h : x.IsOrdinal) (hz : z.IsOrdinal) (hx : x subseteq y) (hy : y in z)
  proof: by
  obtain rfl | hx := h.eq_or_mem_of_subset (hz.mem hy) hx
  · exact hy
  · exact hz.mem_trans hx hy

中文:
定理 mem_of_subset_of_mem
  条件: (h : x.IsOrdinal) (hz : z.IsOrdinal) (hx : x subseteq y) (hy : y in z)
  证明: by
  obtain rfl | hx := h.eq_or_mem_of_subset (hz.mem hy) hx
  · exact hy
  · exact hz.mem_trans hx hy

Depends on / 依赖: eq_or_mem_of_subset, h.eq_or_mem_of_subset, hz.mem, hz.mem_trans, mem_trans
-/
theorem mem_of_subset_of_mem (h : x.IsOrdinal) (hz : z.IsOrdinal) (hx : x subseteq y) (hy : y in z) :
    x in z := by
  obtain rfl | hx := h.eq_or_mem_of_subset (hz.mem hy) hx
  · exact hy
  · exact hz.mem_trans hx hy

/--
theorem `notMem_iff_subset` / 定理 `notMem_iff_subset`

English:
theorem notMem_iff_subset
  given: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  statement: x ∉ y ↔ y subseteq x
  proof: by
  refine ⟨?_, fun hxy hyx => mem_irrefl _ (hxy hyx)⟩
  revert hx hy
  refine Sym2.GameAdd.recursion mem_wf (fun x y IH hx hy hyx z hzy => ?_) x y
  by_contra hzx
  exact hyx (mem_of_subset_of_mem hx hy (IH z x (Sym2.GameAdd.fst_snd hzy) (hy.mem hzy) hx hzx) hzy)

中文:
定理 notMem_iff_subset
  条件: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  结论: x ∉ y ↔ y subseteq x
  证明: by
  refine ⟨?_, fun hxy hyx => mem_irrefl _ (hxy hyx)⟩
  revert hx hy
  refine Sym2.GameAdd.recursion mem_wf (fun x y IH hx hy hyx z hzy => ?_) x y
  by_contra hzx
  exact hyx (mem_of_subset_of_mem hx hy (IH z x (Sym2.GameAdd.fst_snd hzy) (hy.mem hzy) hx hzx) hzy)

Depends on / 依赖: GameAdd, Sym2.GameAdd.fst_snd, Sym2.GameAdd.recursion, fst_snd, hy.mem, mem_irrefl, mem_of_subset_of_mem, mem_wf, recursion, revert
-/
theorem notMem_iff_subset (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ∉ y ↔ y subseteq x := by
  refine ⟨?_, fun hxy hyx => mem_irrefl _ (hxy hyx)⟩
  revert hx hy
  refine Sym2.GameAdd.recursion mem_wf (fun x y IH hx hy hyx z hzy => ?_) x y
  by_contra hzx
  exact hyx (mem_of_subset_of_mem hx hy (IH z x (Sym2.GameAdd.fst_snd hzy) (hy.mem hzy) hx hzx) hzy)

/--
theorem `not_subset_iff_mem` / 定理 `not_subset_iff_mem`

English:
theorem not_subset_iff_mem
  given: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  statement: ¬ x subseteq y ↔ y in x
  proof: by
  rw [not_iff_comm]; rw [notMem_iff_subset hy hx]

中文:
定理 not_subset_iff_mem
  条件: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  结论: ¬ x subseteq y ↔ y in x
  证明: by
  rw [not_iff_comm]; rw [notMem_iff_subset hy hx]

Depends on / 依赖: notMem_iff_subset, not_iff_comm
-/
theorem not_subset_iff_mem (hx : x.IsOrdinal) (hy : y.IsOrdinal) : ¬ x subseteq y ↔ y in x := by
  rw [not_iff_comm]; rw [notMem_iff_subset hy hx]

/--
theorem `mem_or_subset` / 定理 `mem_or_subset`

English:
theorem mem_or_subset
  given: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  statement: x in y ∨ y subseteq x
  proof: by
  rw [or_iff_not_imp_left]; rw [notMem_iff_subset hx hy]
  exact id

中文:
定理 mem_or_subset
  条件: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  结论: x in y ∨ y subseteq x
  证明: by
  rw [or_iff_not_imp_left]; rw [notMem_iff_subset hx hy]
  exact id

Depends on / 依赖: notMem_iff_subset, or_iff_not_imp_left
-/
theorem mem_or_subset (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x in y ∨ y subseteq x := by
  rw [or_iff_not_imp_left]; rw [notMem_iff_subset hx hy]
  exact id

/--
theorem `subset_total` / 定理 `subset_total`

English:
theorem subset_total
  given: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  statement: x subseteq y ∨ y subseteq x
  proof: by
  obtain h | h := mem_or_subset hx hy
  · exact Or.inl (hy.subset_of_mem h)
  · exact Or.inr h

中文:
定理 subset_total
  条件: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  结论: x subseteq y ∨ y subseteq x
  证明: by
  obtain h | h := mem_or_subset hx hy
  · exact Or.inl (hy.subset_of_mem h)
  · exact Or.inr h

Depends on / 依赖: Or.inl, Or.inr, hy.subset_of_mem, mem_or_subset, subset_of_mem
-/
theorem subset_total (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x subseteq y ∨ y subseteq x := by
  obtain h | h := mem_or_subset hx hy
  · exact Or.inl (hy.subset_of_mem h)
  · exact Or.inr h

/--
theorem `mem_trichotomous` / 定理 `mem_trichotomous`

English:
theorem mem_trichotomous
  given: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  statement: x in y ∨ x = y ∨ y in x
  proof: by
  rw [eq_comm]; rw [← subset_iff_eq_or_mem hy hx]
  exact mem_or_subset hx hy

中文:
定理 mem_trichotomous
  条件: (hx : x.IsOrdinal) (hy : y.IsOrdinal)
  结论: x in y ∨ x = y ∨ y in x
  证明: by
  rw [eq_comm]; rw [← subset_iff_eq_or_mem hy hx]
  exact mem_or_subset hx hy

Depends on / 依赖: eq_comm, mem_or_subset, subset_iff_eq_or_mem
-/
theorem mem_trichotomous (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x in y ∨ x = y ∨ y in x := by
  rw [eq_comm]; rw [← subset_iff_eq_or_mem hy hx]
  exact mem_or_subset hx hy

/--
theorem `trichotomous` / 定理 `trichotomous`

English:
theorem trichotomous
  given: (h : x.IsOrdinal)
  statement: Std.Trichotomous (Subrel (· in ·) (· in x))
  proof: Std.trichotomous_of_rel_or_eq_or_rel_swap by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simpa using mem_trichotomous (h.mem ha) (h.mem hb)

@[deprecated (since := "2026-01-24")] protected alias isTrichotomous := IsOrdinal.trichotomous

中文:
定理 trichotomous
  条件: (h : x.IsOrdinal)
  结论: Std.Trichotomous (Subrel (· in ·) (· in x))
  证明: Std.trichotomous_of_rel_or_eq_or_rel_swap by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simpa using mem_trichotomous (h.mem ha) (h.mem hb)

@[deprecated (since := "2026-01-24")] protected alias isTrichotomous := IsOrdinal.trichotomous
-/
protected theorem trichotomous (h : x.IsOrdinal) : Std.Trichotomous (Subrel (· in ·) (· in x)) :=
Std.trichotomous_of_rel_or_eq_or_rel_swap by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simpa using mem_trichotomous (h.mem ha) (h.mem hb)

@[deprecated (since := "2026-01-24")] protected alias isTrichotomous := IsOrdinal.trichotomous

/--
theorem `_root_.ZFSet.isOrdinal_iff_trichotomous` / 定理 `_root_.ZFSet.isOrdinal_iff_trichotomous`

English:
theorem _root_.ZFSet.isOrdinal_iff_trichotomous
  proof: ⟨h.isTransitive, h.trichotomous⟩
  mpr := by
    rintro ⟨h₁, h₂⟩
    rw [isOrdinal_iff_isTrans]
    refine ⟨h₁, ⟨@fun y z w hyz hzw => ?_⟩⟩
    obtain hyw | rfl | hwy := trichotomous_of (Subrel (· in ·) (· in x)) y w
    · exact hyw
    · cases asymm hyz hzw
    · cases mem_wf.asymmetric₃ _ _ _ hyz 

中文:
定理 _root_.ZFSet.isOrdinal_iff_trichotomous
  证明: ⟨h.isTransitive, h.trichotomous⟩
  mpr := by
    rintro ⟨h₁, h₂⟩
    rw [isOrdinal_iff_isTrans]
    refine ⟨h₁, ⟨@fun y z w hyz hzw => ?_⟩⟩
    obtain hyw | rfl | hwy := trichotomous_of (Subrel (· in ·) (· in x)) y w
    · exact hyw
    · cases asymm hyz hzw
    · cases mem_wf.asymmetric₃ _ _ _ hyz 

Depends on / 依赖: h.isTransitive, h.trichotomous, isTransitive, trichotomous
-/
theorem _root_.ZFSet.isOrdinal_iff_trichotomous :
    x.IsOrdinal ↔ x.IsTransitive ∧ Std.Trichotomous (Subrel (· in ·) (· in x)) where
  mp h := ⟨h.isTransitive, h.trichotomous⟩
  mpr := by
    rintro ⟨h₁, h₂⟩
    rw [isOrdinal_iff_isTrans]
    refine ⟨h₁, ⟨@fun y z w hyz hzw => ?_⟩⟩
    obtain hyw | rfl | hwy := trichotomous_of (Subrel (· in ·) (· in x)) y w
    · exact hyw
    · cases asymm hyz hzw
    · cases mem_wf.asymmetric₃ _ _ _ hyz hzw hwy

@[deprecated (since := "2026-01-24")]
alias _root_.ZFSet.isOrdinal_iff_isTrichotomous := _root_.ZFSet.isOrdinal_iff_trichotomous

/--
theorem `isWellOrder` / 定理 `isWellOrder`

English:
theorem isWellOrder
  given: (h : x.IsOrdinal)
  statement: IsWellOrder _ (Subrel (· in ·) (· in x)) where
  proof: (Subrel.relEmbedding _ _).wellFounded mem_wf
  trichotomous := h.trichotomous.1

中文:
定理 isWellOrder
  条件: (h : x.IsOrdinal)
  结论: IsWellOrder _ (Subrel (· in ·) (· in x)) where
  证明: (Subrel.relEmbedding _ _).wellFounded mem_wf
  trichotomous := h.trichotomous.1
-/
protected theorem isWellOrder (h : x.IsOrdinal) : IsWellOrder _ (Subrel (· in ·) (· in x)) where
  wf := (Subrel.relEmbedding _ _).wellFounded mem_wf
  trichotomous := h.trichotomous.1

/--
theorem `_root_.ZFSet.isOrdinal_iff_isWellOrder` / 定理 `_root_.ZFSet.isOrdinal_iff_isWellOrder`

English:
theorem _root_.ZFSet.isOrdinal_iff_isWellOrder
  statement: x.IsOrdinal ↔
  proof: by
  use fun h => ⟨h.isTransitive, h.isWellOrder⟩
  rintro ⟨h₁, h₂⟩
  refine isOrdinal_iff_isTrans.2 ⟨h₁, ?_⟩
  infer_instance

中文:
定理 _root_.ZFSet.isOrdinal_iff_isWellOrder
  结论: x.IsOrdinal ↔
  证明: by
  use fun h => ⟨h.isTransitive, h.isWellOrder⟩
  rintro ⟨h₁, h₂⟩
  refine isOrdinal_iff_isTrans.2 ⟨h₁, ?_⟩
  infer_instance

Depends on / 依赖: h.isTransitive, h.isWellOrder, infer_instance, isOrdinal_iff_isTrans, isTransitive, isWellOrder
-/
theorem _root_.ZFSet.isOrdinal_iff_isWellOrder : x.IsOrdinal ↔
    x.IsTransitive ∧ IsWellOrder _ (Subrel (· in ·) (· in x)) := by
  use fun h => ⟨h.isTransitive, h.isWellOrder⟩
  rintro ⟨h₁, h₂⟩
  refine isOrdinal_iff_isTrans.2 ⟨h₁, ?_⟩
  infer_instance

/--
theorem `rank_lt_iff_mem` / 定理 `rank_lt_iff_mem`

English:
theorem rank_lt_iff_mem
  given: {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y)
  proof: by
  refine ⟨fun h => ?_, rank_lt_of_mem⟩
  rw [← hy.not_subset_iff_mem hx]
  exact fun h' => (rank_mono h').not_gt h

中文:
定理 rank_lt_iff_mem
  条件: {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y)
  证明: by
  refine ⟨fun h => ?_, rank_lt_of_mem⟩
  rw [← hy.not_subset_iff_mem hx]
  exact fun h' => (rank_mono h').not_gt h

Depends on / 依赖: hy.not_subset_iff_mem, not_gt, not_subset_iff_mem, rank_lt_of_mem, rank_mono
-/
theorem rank_lt_iff_mem {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    rank x < rank y ↔ x in y := by
  refine ⟨fun h => ?_, rank_lt_of_mem⟩
  rw [← hy.not_subset_iff_mem hx]
  exact fun h' => (rank_mono h').not_gt h

/--
theorem `rank_le_iff_subset` / 定理 `rank_le_iff_subset`

English:
theorem rank_le_iff_subset
  given: {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y)
  proof: by
  rw [← notMem_iff_subset hy hx]; rw [← rank_lt_iff_mem hy hx]; rw [not_lt]

中文:
定理 rank_le_iff_subset
  条件: {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y)
  证明: by
  rw [← notMem_iff_subset hy hx]; rw [← rank_lt_iff_mem hy hx]; rw [not_lt]

Depends on / 依赖: notMem_iff_subset, not_lt, rank_lt_iff_mem
-/
theorem rank_le_iff_subset {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    rank x <= rank y ↔ x subseteq y := by
  rw [← notMem_iff_subset hy hx]; rw [← rank_lt_iff_mem hy hx]; rw [not_lt]

/--
theorem `rank_inj` / 定理 `rank_inj`

English:
theorem rank_inj
  given: {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y)
  proof: by
  rw [le_antisymm_iff]; rw [subset_antisymm_iff]; rw [rank_le_iff_subset hx hy]; rw [rank_le_iff_subset hy hx]

中文:
定理 rank_inj
  条件: {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y)
  证明: by
  rw [le_antisymm_iff]; rw [subset_antisymm_iff]; rw [rank_le_iff_subset hx hy]; rw [rank_le_iff_subset hy hx]

Depends on / 依赖: le_antisymm_iff, rank_le_iff_subset, subset_antisymm_iff
-/
theorem rank_inj {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    rank x = rank y ↔ x = y := by
  rw [le_antisymm_iff]; rw [subset_antisymm_iff]; rw [rank_le_iff_subset hx hy]; rw [rank_le_iff_subset hy hx]

end IsOrdinal

@[simp]
/--
theorem `isOrdinal_empty` / 定理 `isOrdinal_empty`

English:
theorem isOrdinal_empty
  statement: IsOrdinal ∅
  proof: ⟨isTransitive_empty, fun _ _ H => (notMem_empty _ H).elim⟩

中文:
定理 isOrdinal_empty
  结论: IsOrdinal ∅
  证明: ⟨isTransitive_empty, fun _ _ H => (notMem_empty _ H).elim⟩

Depends on / 依赖: isTransitive_empty, notMem_empty
-/
theorem isOrdinal_empty : IsOrdinal ∅ :=
  ⟨isTransitive_empty, fun _ _ H => (notMem_empty _ H).elim⟩

/--
theorem `isOrdinal_succ` / 定理 `isOrdinal_succ`

English:
theorem isOrdinal_succ
  given: {x : ZFSet} (h : IsOrdinal x)
  statement: IsOrdinal (insert x x)
  proof: by
  refine ⟨fun y hy => ?_, @fun y z w hyz hzw hw => ?_⟩
  · obtain rfl | hy := mem_insert_iff.1 hy
    on_goal 2 => apply (h.subset_of_mem hy).trans
    all_goals simp_all [subset_def]
  · obtain rfl | hw := mem_insert_iff.1 hw
    exacts [h.mem_trans hyz hzw, h.mem_trans' hyz hzw hw]

中文:
定理 isOrdinal_succ
  条件: {x : ZFSet} (h : IsOrdinal x)
  结论: IsOrdinal (insert x x)
  证明: by
  refine ⟨fun y hy => ?_, @fun y z w hyz hzw hw => ?_⟩
  · obtain rfl | hy := mem_insert_iff.1 hy
    on_goal 2 => apply (h.subset_of_mem hy).trans
    all_goals simp_all [subset_def]
  · obtain rfl | hw := mem_insert_iff.1 hw
    exacts [h.mem_trans hyz hzw, h.mem_trans' hyz hzw hw]

Depends on / 依赖: all_goals, exacts, h.mem_trans, h.subset_of_mem, mem_insert_iff, mem_trans, on_goal, subset_def, subset_of_mem
-/
theorem isOrdinal_succ {x : ZFSet} (h : IsOrdinal x) : IsOrdinal (insert x x) := by
  refine ⟨fun y hy => ?_, @fun y z w hyz hzw hw => ?_⟩
  · obtain rfl | hy := mem_insert_iff.1 hy
    on_goal 2 => apply (h.subset_of_mem hy).trans
    all_goals simp_all [subset_def]
  · obtain rfl | hw := mem_insert_iff.1 hw
    exacts [h.mem_trans hyz hzw, h.mem_trans' hyz hzw hw]

end ZFSet

/-! ### Type-theoretic ordinals to von Neumann ordinals -/

namespace Ordinal
open ZFSet

/--
Definition of `toPSet` / `toPSet` 的定义

English:
definition toPSet
  signature: (o : Ordinal.{u})
  body: ⟨o.ToType, fun a => toPSet a⟩
termination_by o
decreasing_by exact a.toOrd.prop

@[simp]

中文:
定义 toPSet
  签名: (o : Ordinal.{u})
  定义体: ⟨o.ToType, fun a => toPSet a⟩
termination_by o
decreasing_by exact a.toOrd.prop

@[simp]

Depends on / 依赖: ToType, a.toOrd.prop, decreasing_by, o.ToType, termination_by, toPSet
-/
noncomputable def toPSet (o : Ordinal.{u}) : PSet.{u} :=
  ⟨o.ToType, fun a => toPSet a⟩
termination_by o
decreasing_by exact a.toOrd.prop

@[simp]
/--
theorem `type_toPSet` / 定理 `type_toPSet`

English:
theorem type_toPSet
  given: (o : Ordinal)
  statement: o.toPSet.Type = o.ToType
  proof: by
  rw [toPSet]
  rfl

中文:
定理 type_toPSet
  条件: (o : Ordinal)
  结论: o.toPSet.Type = o.ToType
  证明: by
  rw [toPSet]
  rfl

Depends on / 依赖: toPSet
-/
theorem type_toPSet (o : Ordinal) : o.toPSet.Type = o.ToType := by
  rw [toPSet]
  rfl

/--
theorem `mem_toPSet_iff` / 定理 `mem_toPSet_iff`

English:
theorem mem_toPSet_iff
  given: {o : Ordinal} {x : PSet}
  statement: x in o.toPSet ↔ exists a < o, x.Equiv a.toPSet
  proof: by
  rw [toPSet]; rw [PSet.mem_def]
  simpa using ((@ToType.mk o).exists_congr_left (p := fun y => x.Equiv y.1.toPSet)).symm

@[simp]

中文:
定理 mem_toPSet_iff
  条件: {o : Ordinal} {x : PSet}
  结论: x in o.toPSet ↔ 存在 a < o, x.Equiv a.toPSet
  证明: by
  rw [toPSet]; rw [PSet.mem_def]
  simpa using ((@ToType.mk o).exists_congr_left (p := fun y => x.Equiv y.1.toPSet)).symm

@[simp]

Depends on / 依赖: PSet.mem_def, ToType, ToType.mk, exists_congr_left, mem_def, toPSet, x.Equiv
-/
theorem mem_toPSet_iff {o : Ordinal} {x : PSet} : x in o.toPSet ↔ exists a < o, x.Equiv a.toPSet := by
  rw [toPSet]; rw [PSet.mem_def]
  simpa using ((@ToType.mk o).exists_congr_left (p := fun y => x.Equiv y.1.toPSet)).symm

@[simp]
/--
theorem `rank_toPSet` / 定理 `rank_toPSet`

English:
theorem rank_toPSet
  given: (o : Ordinal)
  statement: o.toPSet.rank = o
  proof: by
  rw [toPSet]; rw [PSet.rank]
  conv_rhs => rw [← _root_.iSup_succ o]
  convert! ToType.mk.symm.iSup_comp (g := fun x => Order.succ x.1.toPSet.rank)
  rw [rank_toPSet]
termination_by o
decreasing_by rename_i x; exact x.2

中文:
定理 rank_toPSet
  条件: (o : Ordinal)
  结论: o.toPSet.rank = o
  证明: by
  rw [toPSet]; rw [PSet.rank]
  conv_rhs => rw [← _root_.iSup_succ o]
  convert! ToType.mk.symm.iSup_comp (g := fun x => Order.succ x.1.toPSet.rank)
  rw [rank_toPSet]
termination_by o
decreasing_by rename_i x; exact x.2

Depends on / 依赖: Order.succ, PSet.rank, ToType, ToType.mk.symm.iSup_comp, _root_, _root_.iSup_succ, conv_rhs, convert, decreasing_by, iSup_comp, iSup_succ, rank_toPSet, rename_i, termination_by, toPSet, toPSet.rank
-/
theorem rank_toPSet (o : Ordinal) : o.toPSet.rank = o := by
  rw [toPSet]; rw [PSet.rank]
  conv_rhs => rw [← _root_.iSup_succ o]
  convert! ToType.mk.symm.iSup_comp (g := fun x => Order.succ x.1.toPSet.rank)
  rw [rank_toPSet]
termination_by o
decreasing_by rename_i x; exact x.2

/--
Definition of `toZFSet` / `toZFSet` 的定义

English:
definition toZFSet
  signature: (o : Ordinal.{u})
  body: .mk o.toPSet

@[simp]

中文:
定义 toZFSet
  签名: (o : Ordinal.{u})
  定义体: .mk o.toPSet

@[simp]

Depends on / 依赖: o.toPSet, toPSet
-/
noncomputable def toZFSet (o : Ordinal.{u}) : ZFSet.{u} :=
  .mk o.toPSet

@[simp]
/--
theorem `mk_toPSet` / 定理 `mk_toPSet`

English:
theorem mk_toPSet
  given: (o : Ordinal)
  statement: .mk o.toPSet = o.toZFSet
  proof: rfl

中文:
定理 mk_toPSet
  条件: (o : Ordinal)
  结论: .mk o.toPSet = o.toZFSet
  证明: rfl
-/
theorem mk_toPSet (o : Ordinal) : .mk o.toPSet = o.toZFSet :=
  rfl

/--
theorem `mem_toZFSet_iff` / 定理 `mem_toZFSet_iff`

English:
theorem mem_toZFSet_iff
  given: {o : Ordinal} {x : ZFSet}
  statement: x in o.toZFSet ↔ exists a < o, a.toZFSet = x
  proof: by
  induction x using Quotient.ind
  rw [toZFSet]; rw [mk_eq]; rw [ZFSet.mk_mem_iff]; rw [mem_toPSet_iff]
  congr!
  rw [toZFSet]; rw [eq]; rw [PSet.Equiv.comm]

@[simp]

中文:
定理 mem_toZFSet_iff
  条件: {o : Ordinal} {x : ZFSet}
  结论: x in o.toZFSet ↔ 存在 a < o, a.toZFSet = x
  证明: by
  induction x using Quotient.ind
  rw [toZFSet]; rw [mk_eq]; rw [ZFSet.mk_mem_iff]; rw [mem_toPSet_iff]
  congr!
  rw [toZFSet]; rw [eq]; rw [PSet.Equiv.comm]

@[simp]

Depends on / 依赖: PSet.Equiv.comm, Quotient, Quotient.ind, ZFSet.mk_mem_iff, mem_toPSet_iff, mk_eq, mk_mem_iff, toZFSet
-/
theorem mem_toZFSet_iff {o : Ordinal} {x : ZFSet} : x in o.toZFSet ↔ exists a < o, a.toZFSet = x := by
  induction x using Quotient.ind
  rw [toZFSet]; rw [mk_eq]; rw [ZFSet.mk_mem_iff]; rw [mem_toPSet_iff]
  congr!
  rw [toZFSet]; rw [eq]; rw [PSet.Equiv.comm]

@[simp]
/--
theorem `rank_toZFSet` / 定理 `rank_toZFSet`

English:
theorem rank_toZFSet
  given: (o : Ordinal)
  statement: o.toZFSet.rank = o
  proof: rank_toPSet o

@[simp]

中文:
定理 rank_toZFSet
  条件: (o : Ordinal)
  结论: o.toZFSet.rank = o
  证明: rank_toPSet o

@[simp]

Depends on / 依赖: rank_toPSet
-/
theorem rank_toZFSet (o : Ordinal) : o.toZFSet.rank = o :=
  rank_toPSet o

@[simp]
/--
theorem `coe_toZFSet` / 定理 `coe_toZFSet`

English:
theorem coe_toZFSet
  given: {o : Ordinal}
  statement: o.toZFSet = toZFSet '' Iio o
  proof: by
  ext
  simp [mem_toZFSet_iff]

中文:
定理 coe_toZFSet
  条件: {o : Ordinal}
  结论: o.toZFSet = toZFSet '' Iio o
  证明: by
  ext
  simp [mem_toZFSet_iff]

Depends on / 依赖: mem_toZFSet_iff
-/
theorem coe_toZFSet {o : Ordinal} : o.toZFSet = toZFSet '' Iio o := by
  ext
  simp [mem_toZFSet_iff]

/--
theorem `toZFSet_mem_toZFSet_of_lt` / 定理 `toZFSet_mem_toZFSet_of_lt`

English:
theorem toZFSet_mem_toZFSet_of_lt
  given: {a b : Ordinal} (h : a < b)
  proof: by
  rw [mem_toZFSet_iff]
  exact ⟨a, h, rfl⟩

中文:
定理 toZFSet_mem_toZFSet_of_lt
  条件: {a b : Ordinal} (h : a < b)
  证明: by
  rw [mem_toZFSet_iff]
  exact ⟨a, h, rfl⟩
-/
private theorem toZFSet_mem_toZFSet_of_lt {a b : Ordinal} (h : a < b) :
    a.toZFSet in b.toZFSet := by
  rw [mem_toZFSet_iff]
  exact ⟨a, h, rfl⟩

/--
theorem `toZFSet_monotone` / 定理 `toZFSet_monotone`

English:
theorem toZFSet_monotone
  statement: Monotone toZFSet
  proof: by
  intro a b h x hx
  obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hx
  exact toZFSet_mem_toZFSet_of_lt (hc.trans_le h)

@[simp]

中文:
定理 toZFSet_monotone
  结论: Monotone toZFSet
  证明: by
  intro a b h x hx
  obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hx
  exact toZFSet_mem_toZFSet_of_lt (hc.trans_le h)

@[simp]

Depends on / 依赖: hc.trans_le, mem_toZFSet_iff, toZFSet_mem_toZFSet_of_lt, trans_le
-/
theorem toZFSet_monotone : Monotone toZFSet := by
  intro a b h x hx
  obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hx
  exact toZFSet_mem_toZFSet_of_lt (hc.trans_le h)

@[simp]
/--
theorem `toZFSet_mem_toZFSet_iff` / 定理 `toZFSet_mem_toZFSet_iff`

English:
theorem toZFSet_mem_toZFSet_iff
  given: {a b : Ordinal}
  statement: a.toZFSet in b.toZFSet ↔ a < b
  proof: by
  refine ⟨?_, toZFSet_mem_toZFSet_of_lt⟩
  contrapose!
  exact fun h => notMem_of_subset (toZFSet_monotone h)

@[simp]

中文:
定理 toZFSet_mem_toZFSet_iff
  条件: {a b : Ordinal}
  结论: a.toZFSet in b.toZFSet ↔ a < b
  证明: by
  refine ⟨?_, toZFSet_mem_toZFSet_of_lt⟩
  contrapose!
  exact fun h => notMem_of_subset (toZFSet_monotone h)

@[simp]

Depends on / 依赖: contrapose, notMem_of_subset, toZFSet_mem_toZFSet_of_lt, toZFSet_monotone
-/
theorem toZFSet_mem_toZFSet_iff {a b : Ordinal} : a.toZFSet in b.toZFSet ↔ a < b := by
  refine ⟨?_, toZFSet_mem_toZFSet_of_lt⟩
  contrapose!
  exact fun h => notMem_of_subset (toZFSet_monotone h)

@[simp]
/--
theorem `toZFSet_subset_toZFSet_iff` / 定理 `toZFSet_subset_toZFSet_iff`

English:
theorem toZFSet_subset_toZFSet_iff
  given: {a b : Ordinal}
  statement: a.toZFSet subseteq b.toZFSet ↔ a <= b
  proof: by
  refine ⟨?_, fun h => toZFSet_monotone h⟩
  contrapose!
  exact fun h => not_subset_of_mem (toZFSet_mem_toZFSet_of_lt h)

中文:
定理 toZFSet_subset_toZFSet_iff
  条件: {a b : Ordinal}
  结论: a.toZFSet subseteq b.toZFSet ↔ a <= b
  证明: by
  refine ⟨?_, fun h => toZFSet_monotone h⟩
  contrapose!
  exact fun h => not_subset_of_mem (toZFSet_mem_toZFSet_of_lt h)

Depends on / 依赖: contrapose, not_subset_of_mem, toZFSet_mem_toZFSet_of_lt, toZFSet_monotone
-/
theorem toZFSet_subset_toZFSet_iff {a b : Ordinal} : a.toZFSet subseteq b.toZFSet ↔ a <= b := by
  refine ⟨?_, fun h => toZFSet_monotone h⟩
  contrapose!
  exact fun h => not_subset_of_mem (toZFSet_mem_toZFSet_of_lt h)

/--
theorem `toZFSet_strictMono` / 定理 `toZFSet_strictMono`

English:
theorem toZFSet_strictMono
  statement: StrictMono toZFSet
  proof: fun _ _ h => by rw [ssubset_iff_subset_not_subset]; simp [h, h.le]

中文:
定理 toZFSet_strictMono
  结论: StrictMono toZFSet
  证明: fun _ _ h => by rw [ssubset_iff_subset_not_subset]; simp [h, h.le]

Depends on / 依赖: h.le, ssubset_iff_subset_not_subset
-/
theorem toZFSet_strictMono : StrictMono toZFSet :=
  fun _ _ h => by rw [ssubset_iff_subset_not_subset]; simp [h, h.le]

/--
theorem `toZFSet_injective` / 定理 `toZFSet_injective`

English:
theorem toZFSet_injective
  statement: Function.Injective toZFSet
  proof: toZFSet_strictMono.injective

@[simp]

中文:
定理 toZFSet_injective
  结论: Function.Injective toZFSet
  证明: toZFSet_strictMono.injective

@[simp]

Depends on / 依赖: injective, toZFSet_strictMono, toZFSet_strictMono.injective
-/
theorem toZFSet_injective : Function.Injective toZFSet :=
  toZFSet_strictMono.injective

@[simp]
/--
theorem `toZFSet_zero` / 定理 `toZFSet_zero`

English:
theorem toZFSet_zero
  statement: toZFSet 0 = ∅
  proof: by
  ext; simp [mem_toZFSet_iff]

@[simp]

中文:
定理 toZFSet_zero
  结论: toZFSet 0 = ∅
  证明: by
  ext; simp [mem_toZFSet_iff]

@[simp]

Depends on / 依赖: mem_toZFSet_iff
-/
theorem toZFSet_zero : toZFSet 0 = ∅ := by
  ext; simp [mem_toZFSet_iff]

@[simp]
/--
theorem `toZFSet_add_one` / 定理 `toZFSet_add_one`

English:
theorem toZFSet_add_one
  given: (o : Ordinal)
  statement: toZFSet (o + 1) = insert (toZFSet o) (toZFSet o)
  proof: by
  aesop (add simp [mem_toZFSet_iff, le_iff_eq_or_lt])

@[deprecated toZFSet_add_one (since := "2026-02-24")]

中文:
定理 toZFSet_add_one
  条件: (o : Ordinal)
  结论: toZFSet (o + 1) = insert (toZFSet o) (toZFSet o)
  证明: by
  aesop (add simp [mem_toZFSet_iff, le_iff_eq_or_lt])

@[deprecated toZFSet_add_one (since := "2026-02-24")]

Depends on / 依赖: le_iff_eq_or_lt, mem_toZFSet_iff
-/
theorem toZFSet_add_one (o : Ordinal) : toZFSet (o + 1) = insert (toZFSet o) (toZFSet o) := by
  aesop (add simp [mem_toZFSet_iff, le_iff_eq_or_lt])

@[deprecated toZFSet_add_one (since := "2026-02-24")]
/--
theorem `toZFSet_succ` / 定理 `toZFSet_succ`

English:
theorem toZFSet_succ
  given: (o : Ordinal)
  statement: toZFSet (Order.succ o) = insert (toZFSet o) (toZFSet o)
  proof: toZFSet_add_one o

@[simp]

中文:
定理 toZFSet_succ
  条件: (o : Ordinal)
  结论: toZFSet (Order.succ o) = insert (toZFSet o) (toZFSet o)
  证明: toZFSet_add_one o

@[simp]

Depends on / 依赖: toZFSet_add_one
-/
theorem toZFSet_succ (o : Ordinal) : toZFSet (Order.succ o) = insert (toZFSet o) (toZFSet o) :=
  toZFSet_add_one o

@[simp]
/--
theorem `card_toZFSet` / 定理 `card_toZFSet`

English:
theorem card_toZFSet
  given: (o : Ordinal)
  statement: (toZFSet o).card = o.card
  proof: by
  simpa [← coe_toZFSet, cardinalMk_coe_sort, Cardinal.mk_Iio_ordinal, ← lift_card] using
    Cardinal.mk_image_eq (s := Iio o) toZFSet_injective

中文:
定理 card_toZFSet
  条件: (o : Ordinal)
  结论: (toZFSet o).card = o.card
  证明: by
  simpa [← coe_toZFSet, cardinalMk_coe_sort, Cardinal.mk_Iio_ordinal, ← lift_card] using
    Cardinal.mk_image_eq (s := Iio o) toZFSet_injective

Depends on / 依赖: Cardinal, Cardinal.mk_Iio_ordinal, Cardinal.mk_image_eq, cardinalMk_coe_sort, coe_toZFSet, lift_card, mk_Iio_ordinal, mk_image_eq, toZFSet_injective
-/
theorem card_toZFSet (o : Ordinal) : (toZFSet o).card = o.card := by
  simpa [← coe_toZFSet, cardinalMk_coe_sort, Cardinal.mk_Iio_ordinal, ← lift_card] using
    Cardinal.mk_image_eq (s := Iio o) toZFSet_injective

end Ordinal

namespace ZFSet
open Ordinal

/--
theorem `isOrdinal_toZFSet` / 定理 `isOrdinal_toZFSet`

English:
theorem isOrdinal_toZFSet
  given: (o : Ordinal)
  statement: IsOrdinal o.toZFSet
  proof: by
  refine ⟨fun x hx y hy => ?_, fun {z y x} hz hy hx => ?_⟩
  all_goals
    obtain ⟨a, ha, rfl⟩ := mem_toZFSet_iff.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_toZFSet_iff.1 hy
  · exact toZFSet_mem_toZFSet_iff.2 (hb.trans ha)
  · obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hz
    exact toZFSet_mem_toZFSet_if

中文:
定理 isOrdinal_toZFSet
  条件: (o : Ordinal)
  结论: IsOrdinal o.toZFSet
  证明: by
  refine ⟨fun x hx y hy => ?_, fun {z y x} hz hy hx => ?_⟩
  all_goals
    obtain ⟨a, ha, rfl⟩ := mem_toZFSet_iff.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_toZFSet_iff.1 hy
  · exact toZFSet_mem_toZFSet_iff.2 (hb.trans ha)
  · obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hz
    exact toZFSet_mem_toZFSet_if

Depends on / 依赖: all_goals, hb.trans, hc.trans, mem_toZFSet_iff, toZFSet_mem_toZFSet_iff
-/
theorem isOrdinal_toZFSet (o : Ordinal) : IsOrdinal o.toZFSet := by
  refine ⟨fun x hx y hy => ?_, fun {z y x} hz hy hx => ?_⟩
  all_goals
    obtain ⟨a, ha, rfl⟩ := mem_toZFSet_iff.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_toZFSet_iff.1 hy
  · exact toZFSet_mem_toZFSet_iff.2 (hb.trans ha)
  · obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hz
    exact toZFSet_mem_toZFSet_iff.2 (hc.trans hb)

/--
theorem `IsOrdinal.toZFSet_rank_eq` / 定理 `IsOrdinal.toZFSet_rank_eq`

English:
theorem IsOrdinal.toZFSet_rank_eq
  given: {x : ZFSet} (hx : IsOrdinal x)
  statement: x.rank.toZFSet = x
  proof: (IsOrdinal.rank_inj (isOrdinal_toZFSet _) hx).1 (rank_toZFSet _)

中文:
定理 IsOrdinal.toZFSet_rank_eq
  条件: {x : ZFSet} (hx : IsOrdinal x)
  结论: x.rank.toZFSet = x
  证明: (IsOrdinal.rank_inj (isOrdinal_toZFSet _) hx).1 (rank_toZFSet _)

Depends on / 依赖: IsOrdinal, IsOrdinal.rank_inj, isOrdinal_toZFSet, rank_inj, rank_toZFSet
-/
theorem IsOrdinal.toZFSet_rank_eq {x : ZFSet} (hx : IsOrdinal x) : x.rank.toZFSet = x :=
  (IsOrdinal.rank_inj (isOrdinal_toZFSet _) hx).1 (rank_toZFSet _)

/--
theorem `isOrdinal_iff_mem_range_toZFSet` / 定理 `isOrdinal_iff_mem_range_toZFSet`

English:
theorem isOrdinal_iff_mem_range_toZFSet
  given: {x : ZFSet.{u}}
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← h.toZFSet_rank_eq]
    exact Set.mem_range_self _
  · rintro ⟨a, rfl⟩
    exact isOrdinal_toZFSet a

中文:
定理 isOrdinal_iff_mem_range_toZFSet
  条件: {x : ZFSet.{u}}
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← h.toZFSet_rank_eq]
    exact Set.mem_range_self _
  · rintro ⟨a, rfl⟩
    exact isOrdinal_toZFSet a

Depends on / 依赖: Set.mem_range_self, h.toZFSet_rank_eq, isOrdinal_toZFSet, mem_range_self, toZFSet_rank_eq
-/
theorem isOrdinal_iff_mem_range_toZFSet {x : ZFSet.{u}} :
    IsOrdinal x ↔ x in Set.range toZFSet.{u} := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← h.toZFSet_rank_eq]
    exact Set.mem_range_self _
  · rintro ⟨a, rfl⟩
    exact isOrdinal_toZFSet a

set_option backward.isDefEq.respectTransparency false in
/-- `Ordinal` is order-equivalent to the type of von Neumann ordinals. -/
@[simps apply symm_apply]
/--
Definition of `_root_.Ordinal.toZFSetIso` / `_root_.Ordinal.toZFSetIso` 的定义

English:
definition _root_.Ordinal.toZFSetIso
  signature: : Ordinal ≃o {x // ZFSet.IsOrdinal x} where
  body: ⟨_, isOrdinal_toZFSet o⟩
  invFun x := rank x.1
  left_inv o := rank_toZFSet o
  right_inv := fun ⟨x, hx⟩ => by simpa using hx.toZFSet_rank_eq
  map_rel_iff' {a b} := by simp

中文:
定义 _root_.Ordinal.toZFSetIso
  签名: : Ordinal ≃o {x // ZFSet.IsOrdinal x} where
  定义体: ⟨_, isOrdinal_toZFSet o⟩
  invFun x := rank x.1
  left_inv o := rank_toZFSet o
  right_inv := fun ⟨x, hx⟩ => by simpa using hx.toZFSet_rank_eq
  map_rel_iff' {a b} := by simp

Depends on / 依赖: isOrdinal_toZFSet
-/
noncomputable def _root_.Ordinal.toZFSetIso : Ordinal ≃o {x // ZFSet.IsOrdinal x} where
  toFun o := ⟨_, isOrdinal_toZFSet o⟩
  invFun x := rank x.1
  left_inv o := rank_toZFSet o
  right_inv := fun ⟨x, hx⟩ => by simpa using hx.toZFSet_rank_eq
  map_rel_iff' {a b} := by simp

end ZFSet
