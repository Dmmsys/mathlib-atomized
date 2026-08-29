/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.ModularLattice
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Nontriviality
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Tactic.Attr.Core

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
* `IsAtom a` indicates that the only element below `a` is `⊥`.
* `IsCoatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
* `IsAtomic` indicates that every element other than `⊥` is above an atom.
* `IsCoatomic` indicates that every element other than `⊤` is below a coatom.
* `IsAtomistic` indicates that every element is the `sSup` of a set of atoms.
* `IsCoatomistic` indicates that every element is the `sInf` of a set of coatoms.
* `IsStronglyAtomic` indicates that for all `a < b`, there is some `x` with `a ⋖ x ≤ b`.
* `IsStronglyCoatomic` indicates that for all `a < b`, there is some `x` with `a ≤ x ⋖ b`.

### Simple Lattices
* `IsSimpleOrder` indicates that an order has only two unique elements, `⊥` and `⊤`.
* `IsSimpleOrder.boundedOrder`
* `IsSimpleOrder.distribLattice`
* Given an instance of `IsSimpleOrder`, we provide the following definitions. These are not
  made global instances as they contain data :
  * `IsSimpleOrder.booleanAlgebra`
  * `IsSimpleOrder.completeLattice`
  * `IsSimpleOrder.completeBooleanAlgebra`

## Main results
* `isAtom_dual_iff_isCoatom` and `isCoatom_dual_iff_isAtom` express the (definitional) duality
  of `IsAtom` and `IsCoatom`.
* `isSimpleOrder_iff_isAtom_top` and `isSimpleOrder_iff_isCoatom_bot` express the
  connection between atoms, coatoms, and simple lattices
* `IsCompl.isAtom_iff_isCoatom` and `IsCompl.isCoatom_if_isAtom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
* `isAtomic_iff_isCoatomic`: A modular complemented lattice is atomic iff it is coatomic.

-/

@[expose] public section

open Order

variable {ι : Sort*} {α β : Type*}

section Atoms

section IsAtom

section Preorder

variable [Preorder α] [OrderBot α] {a b x : α}

/--
Definition of `IsAtom` / `IsAtom` 的定义

English:
definition IsAtom
  signature: (a : α)
  body: a != ⊥ ∧ forall b, b < a -> b = ⊥

中文:
定义 IsAtom
  签名: (a : α)
  定义体: a != ⊥ ∧ forall b, b < a -> b = ⊥
-/
def IsAtom (a : α) : Prop :=
  a != ⊥ ∧ forall b, b < a -> b = ⊥

/--
theorem `IsAtom.Iic` / 定理 `IsAtom.Iic`

English:
theorem IsAtom.Iic
  given: (ha : IsAtom a) (hax : a <= x)
  statement: IsAtom (⟨a, hax⟩ : Set.Iic x)
  proof: ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, _⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

中文:
定理 IsAtom.左无界右闭区间
  条件: (ha : IsAtom a) (hax : a <= x)
  结论: IsAtom (⟨a, hax⟩ : 集合.左无界右闭区间 x)
  证明: ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, _⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, mk_eq_mk
-/
theorem IsAtom.Iic (ha : IsAtom a) (hax : a <= x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, _⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

/--
theorem `IsAtom.of_isAtom_coe_Iic` / 定理 `IsAtom.of_isAtom_coe_Iic`

English:
theorem IsAtom.of_isAtom_coe_Iic
  given: {a : Set.Iic x} (ha : IsAtom a)
  statement: IsAtom (a : α)
  proof: ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩

中文:
定理 IsAtom.of_isAtom_coe_Iic
  条件: {a : 集合.左无界右闭区间 x} (ha : IsAtom a)
  结论: IsAtom (a : α)
  证明: ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩

Depends on / 依赖: Subtype, Subtype.ext, Subtype.mk_eq_mk, a.prop, hba.le.trans, mk_eq_mk
-/
theorem IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩

/--
theorem `isAtom_iff_le_of_ge` / 定理 `isAtom_iff_le_of_ge`

English:
theorem isAtom_iff_le_of_ge
  statement: IsAtom a ↔ a != ⊥ ∧ forall b != ⊥, b <= a -> a <= b
  proof: and_congr Iff.rfl
    forall_congr' fun b => by
      simp only [Ne, @not_imp_comm (b = ⊥), Classical.not_imp, lt_iff_le_not_ge]

中文:
定理 isAtom_iff_le_of_ge
  结论: IsAtom a ↔ a != ⊥ ∧ 对任意 b != ⊥, b <= a -> a <= b
  证明: and_congr Iff.rfl
    forall_congr' fun b => by
      simp only [Ne, @not_imp_comm (b = ⊥), Classical.not_imp, lt_iff_le_not_ge]

Depends on / 依赖: Classical, Classical.not_imp, Iff.rfl, and_congr, forall_congr, lt_iff_le_not_ge, not_imp, not_imp_comm
-/
theorem isAtom_iff_le_of_ge : IsAtom a ↔ a != ⊥ ∧ forall b != ⊥, b <= a -> a <= b :=
and_congr Iff.rfl
    forall_congr' fun b => by
      simp only [Ne, @not_imp_comm (b = ⊥), Classical.not_imp, lt_iff_le_not_ge]

/--
lemma `IsAtom.ne_bot` / 引理 `IsAtom.ne_bot`

English:
lemma IsAtom.ne_bot
  given: (ha : IsAtom a)
  statement: a != ⊥
  proof: ha.1

中文:
引理 IsAtom.ne_bot
  条件: (ha : IsAtom a)
  结论: a != ⊥
  证明: ha.1
-/
lemma IsAtom.ne_bot (ha : IsAtom a) : a != ⊥ := ha.1

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderBot α] {a b x : α}

/--
theorem `IsAtom.lt_iff` / 定理 `IsAtom.lt_iff`

English:
theorem IsAtom.lt_iff
  given: (h : IsAtom a)
  statement: x < a ↔ x = ⊥
  proof: ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩

中文:
定理 IsAtom.lt_iff
  条件: (h : IsAtom a)
  结论: x < a ↔ x = ⊥
  证明: ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩

Depends on / 依赖: bot_lt, hx.symm
-/
theorem IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ :=
  ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩

/--
theorem `IsAtom.le_iff` / 定理 `IsAtom.le_iff`

English:
theorem IsAtom.le_iff
  given: (h : IsAtom a)
  statement: x <= a ↔ x = ⊥ ∨ x = a
  proof: by rw [le_iff_lt_or_eq, h.lt_iff]

中文:
定理 IsAtom.le_iff
  条件: (h : IsAtom a)
  结论: x <= a ↔ x = ⊥ ∨ x = a
  证明: by rw [le_iff_lt_or_eq, h.lt_iff]

Depends on / 依赖: h.lt_iff, le_iff_lt_or_eq, lt_iff
-/
theorem IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a := by rw [le_iff_lt_or_eq, h.lt_iff]

/--
lemma `IsAtom.bot_lt` / 引理 `IsAtom.bot_lt`

English:
lemma IsAtom.bot_lt
  given: (h : IsAtom a)
  statement: ⊥ < a
  proof: h.lt_iff.mpr rfl

中文:
引理 IsAtom.bot_lt
  条件: (h : IsAtom a)
  结论: ⊥ < a
  证明: h.lt_iff.mpr rfl

Depends on / 依赖: h.lt_iff.mpr, lt_iff
-/
lemma IsAtom.bot_lt (h : IsAtom a) : ⊥ < a :=
  h.lt_iff.mpr rfl

/--
lemma `IsAtom.le_iff_eq` / 引理 `IsAtom.le_iff_eq`

English:
lemma IsAtom.le_iff_eq
  given: (ha : IsAtom a) (hb : b != ⊥)
  statement: b <= a ↔ b = a
  proof: ha.le_iff.trans or_iff_right hb

中文:
引理 IsAtom.le_iff_eq
  条件: (ha : IsAtom a) (hb : b != ⊥)
  结论: b <= a ↔ b = a
  证明: ha.le_iff.trans or_iff_right hb

Depends on / 依赖: ha.le_iff.trans, le_iff, or_iff_right
-/
lemma IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= a ↔ b = a :=
ha.le_iff.trans or_iff_right hb

/--
lemma `IsAtom.ne_iff_eq_bot` / 引理 `IsAtom.ne_iff_eq_bot`

English:
lemma IsAtom.ne_iff_eq_bot
  given: (ha : IsAtom a) (hba : b <= a)
  statement: b != a ↔ b = ⊥ where
  proof: (ha.le_iff.1 hba).resolve_right
  mpr := by rintro rfl; exact ha.ne_bot.symm

中文:
引理 IsAtom.ne_iff_eq_bot
  条件: (ha : IsAtom a) (hba : b <= a)
  结论: b != a ↔ b = ⊥ where
  证明: (ha.le_iff.1 hba).resolve_right
  mpr := by rintro rfl; exact ha.ne_bot.symm

Depends on / 依赖: ha.le_iff, le_iff, resolve_right
-/
lemma IsAtom.ne_iff_eq_bot (ha : IsAtom a) (hba : b <= a) : b != a ↔ b = ⊥ where
  mp := (ha.le_iff.1 hba).resolve_right
  mpr := by rintro rfl; exact ha.ne_bot.symm

/--
lemma `IsAtom.ne_bot_iff_eq` / 引理 `IsAtom.ne_bot_iff_eq`

English:
lemma IsAtom.ne_bot_iff_eq
  given: (ha : IsAtom a) (hba : b <= a)
  statement: b != ⊥ ↔ b = a
  proof: (ha.ne_iff_eq_bot hba).not_right.symm

中文:
引理 IsAtom.ne_bot_iff_eq
  条件: (ha : IsAtom a) (hba : b <= a)
  结论: b != ⊥ ↔ b = a
  证明: (ha.ne_iff_eq_bot hba).not_right.symm

Depends on / 依赖: ha.ne_iff_eq_bot, ne_iff_eq_bot, not_right, not_right.symm
-/
lemma IsAtom.ne_bot_iff_eq (ha : IsAtom a) (hba : b <= a) : b != ⊥ ↔ b = a :=
  (ha.ne_iff_eq_bot hba).not_right.symm

/--
theorem `IsAtom.Iic_eq` / 定理 `IsAtom.Iic_eq`

English:
theorem IsAtom.Iic_eq
  given: (h : IsAtom a)
  statement: Set.Iic a = {⊥, a}
  proof: Set.ext fun _ => h.le_iff

中文:
定理 IsAtom.Iic_eq
  条件: (h : IsAtom a)
  结论: 集合.左无界右闭区间 a = {⊥, a}
  证明: Set.ext fun _ => h.le_iff

Depends on / 依赖: Set.ext, h.le_iff, le_iff
-/
theorem IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a} :=
  Set.ext fun _ => h.le_iff

/--
lemma `Set.Iio_eq_singleton_bot_iff` / 引理 `Set.Iio_eq_singleton_bot_iff`

English:
lemma Set.Iio_eq_singleton_bot_iff
  statement: Iio a = {⊥} ↔ IsAtom a
  proof: by
  simp [IsAtom, superset_antisymm_iff, bot_lt_iff_ne_bot]

@[simp]

中文:
引理 集合.Iio_eq_singleton_bot_iff
  结论: 左无界右开区间 a = {⊥} ↔ IsAtom a
  证明: by
  simp [IsAtom, superset_antisymm_iff, bot_lt_iff_ne_bot]

@[simp]

Depends on / 依赖: IsAtom, bot_lt_iff_ne_bot, superset_antisymm_iff
-/
lemma Set.Iio_eq_singleton_bot_iff : Iio a = {⊥} ↔ IsAtom a := by
  simp [IsAtom, superset_antisymm_iff, bot_lt_iff_ne_bot]

@[simp]
/--
theorem `bot_covBy_iff` / 定理 `bot_covBy_iff`

English:
theorem bot_covBy_iff
  statement: ⊥ ⋖ a ↔ IsAtom a
  proof: by
  simp only [CovBy, bot_lt_iff_ne_bot, IsAtom, not_imp_not]

alias ⟨CovBy.is_atom, IsAtom.bot_covBy⟩ := bot_covBy_iff

中文:
定理 bot_covBy_iff
  结论: ⊥ ⋖ a ↔ IsAtom a
  证明: by
  simp only [CovBy, bot_lt_iff_ne_bot, IsAtom, not_imp_not]

alias ⟨CovBy.is_atom, IsAtom.bot_covBy⟩ := bot_covBy_iff

Depends on / 依赖: IsAtom, bot_lt_iff_ne_bot, not_imp_not
-/
theorem bot_covBy_iff : ⊥ ⋖ a ↔ IsAtom a := by
  simp only [CovBy, bot_lt_iff_ne_bot, IsAtom, not_imp_not]

alias ⟨CovBy.is_atom, IsAtom.bot_covBy⟩ := bot_covBy_iff

end PartialOrder

section Frame
variable [Frame α] {f : ι -> α} {s : Set α} {a : α}

/--
lemma `IsAtom.le_iSup` / 引理 `IsAtom.le_iSup`

English:
lemma IsAtom.le_iSup
  given: (ha : IsAtom a)
  statement: a <= iSup f ↔ exists i, a <= f i
  proof: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_trans hi (le_iSup _ _)⟩
  change (a <= ⨆ i, f i) -> _
  refine fun h => of_not_not fun ha' => ?_
  push Not at ha'
  have ha'' : Disjoint a (⨆ i, f i) :=
disjoint_iSup_iff.2 fun i => fun x hxa hxf => le_bot_iff.2 of_not_not fun hx =>
      have hxa : x < a := (le_iff_eq_or_lt.1 hxa).resolve_left (by rintro rfl; exact ha' _ hxf)
      hx (ha.2 _ hxa)
  obtain rfl := le_bot_iff.1 (ha'' le_rfl h)
  exact ha.1 rfl

中文:
引理 IsAtom.le_iSup
  条件: (ha : IsAtom a)
  结论: a <= iSup f ↔ 存在 i, a <= f i
  证明: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_trans hi (le_iSup _ _)⟩
  change (a <= ⨆ i, f i) -> _
  refine fun h => of_not_not fun ha' => ?_
  push Not at ha'
  have ha'' : Disjoint a (⨆ i, f i) :=
disjoint_iSup_iff.2 fun i => fun x hxa hxf => le_bot_iff.2 of_not_not fun hx =>
      have hxa : x < a := (le_iff_eq_or_lt.1 hxa).resolve_left (by rintro rfl; exact ha' _ hxf)
      hx (ha.2 _ hxa)
  obtain rfl := le_bot_iff.1 (ha'' le_rfl h)
  exact ha.1 rfl
-/
protected lemma IsAtom.le_iSup (ha : IsAtom a) : a <= iSup f ↔ exists i, a <= f i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_trans hi (le_iSup _ _)⟩
  change (a <= ⨆ i, f i) -> _
  refine fun h => of_not_not fun ha' => ?_
  push Not at ha'
  have ha'' : Disjoint a (⨆ i, f i) :=
disjoint_iSup_iff.2 fun i => fun x hxa hxf => le_bot_iff.2 of_not_not fun hx =>
      have hxa : x < a := (le_iff_eq_or_lt.1 hxa).resolve_left (by rintro rfl; exact ha' _ hxf)
      hx (ha.2 _ hxa)
  obtain rfl := le_bot_iff.1 (ha'' le_rfl h)
  exact ha.1 rfl

/--
lemma `IsAtom.le_sSup` / 引理 `IsAtom.le_sSup`

English:
lemma IsAtom.le_sSup
  given: (ha : IsAtom a)
  statement: a <= sSup s ↔ exists b in s, a <= b
  proof: by
  simp [sSup_eq_iSup', ha.le_iSup]

中文:
引理 IsAtom.le_sSup
  条件: (ha : IsAtom a)
  结论: a <= sSup s ↔ 存在 b in s, a <= b
  证明: by
  simp [sSup_eq_iSup', ha.le_iSup]
-/
protected lemma IsAtom.le_sSup (ha : IsAtom a) : a <= sSup s ↔ exists b in s, a <= b := by
  simp [sSup_eq_iSup', ha.le_iSup]

end Frame
end IsAtom

section IsCoatom

section Preorder

variable [Preorder α]

/--
Definition of `IsCoatom` / `IsCoatom` 的定义

English:
definition IsCoatom
  signature: [OrderTop α] (a : α)
  body: a != ⊤ ∧ forall b, a < b -> b = ⊤

@[simp]

中文:
定义 IsCoatom
  签名: [有顶序 α] (a : α)
  定义体: a != ⊤ ∧ forall b, a < b -> b = ⊤

@[simp]
-/
def IsCoatom [OrderTop α] (a : α) : Prop :=
  a != ⊤ ∧ forall b, a < b -> b = ⊤

@[simp]
/--
theorem `isCoatom_dual_iff_isAtom` / 定理 `isCoatom_dual_iff_isAtom`

English:
theorem isCoatom_dual_iff_isAtom
  given: [OrderBot α] {a : α}
  proof: Iff.rfl

@[simp]

中文:
定理 isCoatom_dual_iff_isAtom
  条件: [有底序 α] {a : α}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem isCoatom_dual_iff_isAtom [OrderBot α] {a : α} :
    IsCoatom (OrderDual.toDual a) ↔ IsAtom a :=
  Iff.rfl

@[simp]
/--
theorem `isAtom_dual_iff_isCoatom` / 定理 `isAtom_dual_iff_isCoatom`

English:
theorem isAtom_dual_iff_isCoatom
  given: [OrderTop α] {a : α}
  proof: Iff.rfl

alias ⟨_, IsAtom.dual⟩ := isCoatom_dual_iff_isAtom

alias ⟨_, IsCoatom.dual⟩ := isAtom_dual_iff_isCoatom

中文:
定理 isAtom_dual_iff_isCoatom
  条件: [有顶序 α] {a : α}
  证明: Iff.rfl

alias ⟨_, IsAtom.dual⟩ := isCoatom_dual_iff_isAtom

alias ⟨_, IsCoatom.dual⟩ := isAtom_dual_iff_isCoatom

Depends on / 依赖: Iff.rfl
-/
theorem isAtom_dual_iff_isCoatom [OrderTop α] {a : α} :
    IsAtom (OrderDual.toDual a) ↔ IsCoatom a :=
  Iff.rfl

alias ⟨_, IsAtom.dual⟩ := isCoatom_dual_iff_isAtom

alias ⟨_, IsCoatom.dual⟩ := isAtom_dual_iff_isCoatom

variable [OrderTop α] {a x : α}

/--
theorem `IsCoatom.Ici` / 定理 `IsCoatom.Ici`

English:
theorem IsCoatom.Ici
  given: (ha : IsCoatom a) (hax : x <= a)
  statement: IsCoatom (⟨a, hax⟩ : Set.Ici x)
  proof: ha.dual.Iic hax

中文:
定理 IsCoatom.左闭右无界区间
  条件: (ha : IsCoatom a) (hax : x <= a)
  结论: IsCoatom (⟨a, hax⟩ : 集合.左闭右无界区间 x)
  证明: ha.dual.Iic hax

Depends on / 依赖: ha.dual.Iic
-/
theorem IsCoatom.Ici (ha : IsCoatom a) (hax : x <= a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ha.dual.Iic hax

/--
theorem `IsCoatom.of_isCoatom_coe_Ici` / 定理 `IsCoatom.of_isCoatom_coe_Ici`

English:
theorem IsCoatom.of_isCoatom_coe_Ici
  given: {a : Set.Ici x} (ha : IsCoatom a)
  statement: IsCoatom (a : α)
  proof: @IsAtom.of_isAtom_coe_Iic αᵒᵈ _ _ x a ha

中文:
定理 IsCoatom.of_isCoatom_coe_Ici
  条件: {a : 集合.左闭右无界区间 x} (ha : IsCoatom a)
  结论: IsCoatom (a : α)
  证明: @IsAtom.of_isAtom_coe_Iic αᵒᵈ _ _ x a ha

Depends on / 依赖: IsAtom, IsAtom.of_isAtom_coe_Iic, of_isAtom_coe_Iic
-/
theorem IsCoatom.of_isCoatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  @IsAtom.of_isAtom_coe_Iic αᵒᵈ _ _ x a ha

/--
theorem `isCoatom_iff_ge_of_le` / 定理 `isCoatom_iff_ge_of_le`

English:
theorem isCoatom_iff_ge_of_le
  statement: IsCoatom a ↔ a != ⊤ ∧ forall b != ⊤, a <= b -> b <= a
  proof: isAtom_iff_le_of_ge (α := αᵒᵈ)

中文:
定理 isCoatom_iff_ge_of_le
  结论: IsCoatom a ↔ a != ⊤ ∧ 对任意 b != ⊤, a <= b -> b <= a
  证明: isAtom_iff_le_of_ge (α := αᵒᵈ)

Depends on / 依赖: isAtom_iff_le_of_ge
-/
theorem isCoatom_iff_ge_of_le : IsCoatom a ↔ a != ⊤ ∧ forall b != ⊤, a <= b -> b <= a :=
  isAtom_iff_le_of_ge (α := αᵒᵈ)

/--
lemma `IsCoatom.ne_top` / 引理 `IsCoatom.ne_top`

English:
lemma IsCoatom.ne_top
  given: (ha : IsCoatom a)
  statement: a != ⊤
  proof: ha.1

中文:
引理 IsCoatom.ne_top
  条件: (ha : IsCoatom a)
  结论: a != ⊤
  证明: ha.1
-/
lemma IsCoatom.ne_top (ha : IsCoatom a) : a != ⊤ := ha.1

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderTop α] {a b x : α}

/--
theorem `IsCoatom.lt_iff` / 定理 `IsCoatom.lt_iff`

English:
theorem IsCoatom.lt_iff
  given: (h : IsCoatom a)
  statement: a < x ↔ x = ⊤
  proof: h.dual.lt_iff

中文:
定理 IsCoatom.lt_iff
  条件: (h : IsCoatom a)
  结论: a < x ↔ x = ⊤
  证明: h.dual.lt_iff

Depends on / 依赖: h.dual.lt_iff, lt_iff
-/
theorem IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤ :=
  h.dual.lt_iff

/--
theorem `IsCoatom.le_iff` / 定理 `IsCoatom.le_iff`

English:
theorem IsCoatom.le_iff
  given: (h : IsCoatom a)
  statement: a <= x ↔ x = ⊤ ∨ x = a
  proof: h.dual.le_iff

中文:
定理 IsCoatom.le_iff
  条件: (h : IsCoatom a)
  结论: a <= x ↔ x = ⊤ ∨ x = a
  证明: h.dual.le_iff

Depends on / 依赖: h.dual.le_iff, le_iff
-/
theorem IsCoatom.le_iff (h : IsCoatom a) : a <= x ↔ x = ⊤ ∨ x = a :=
  h.dual.le_iff

/--
lemma `IsCoatom.lt_top` / 引理 `IsCoatom.lt_top`

English:
lemma IsCoatom.lt_top
  given: (h : IsCoatom a)
  statement: a < ⊤
  proof: h.lt_iff.mpr rfl

中文:
引理 IsCoatom.lt_top
  条件: (h : IsCoatom a)
  结论: a < ⊤
  证明: h.lt_iff.mpr rfl

Depends on / 依赖: h.lt_iff.mpr, lt_iff
-/
lemma IsCoatom.lt_top (h : IsCoatom a) : a < ⊤ :=
  h.lt_iff.mpr rfl

/--
lemma `IsCoatom.le_iff_eq` / 引理 `IsCoatom.le_iff_eq`

English:
lemma IsCoatom.le_iff_eq
  given: (ha : IsCoatom a) (hb : b != ⊤)
  statement: a <= b ↔ b = a
  proof: ha.dual.le_iff_eq hb

中文:
引理 IsCoatom.le_iff_eq
  条件: (ha : IsCoatom a) (hb : b != ⊤)
  结论: a <= b ↔ b = a
  证明: ha.dual.le_iff_eq hb

Depends on / 依赖: ha.dual.le_iff_eq, le_iff_eq
-/
lemma IsCoatom.le_iff_eq (ha : IsCoatom a) (hb : b != ⊤) : a <= b ↔ b = a := ha.dual.le_iff_eq hb

/--
lemma `IsCoatom.ne_iff_eq_top` / 引理 `IsCoatom.ne_iff_eq_top`

English:
lemma IsCoatom.ne_iff_eq_top
  given: (ha : IsCoatom a) (hab : a <= b)
  statement: b != a ↔ b = ⊤ where
  proof: (ha.le_iff.1 hab).resolve_right
  mpr := by rintro rfl; exact ha.ne_top.symm

中文:
引理 IsCoatom.ne_iff_eq_top
  条件: (ha : IsCoatom a) (hab : a <= b)
  结论: b != a ↔ b = ⊤ where
  证明: (ha.le_iff.1 hab).resolve_right
  mpr := by rintro rfl; exact ha.ne_top.symm

Depends on / 依赖: ha.le_iff, le_iff, resolve_right
-/
lemma IsCoatom.ne_iff_eq_top (ha : IsCoatom a) (hab : a <= b) : b != a ↔ b = ⊤ where
  mp := (ha.le_iff.1 hab).resolve_right
  mpr := by rintro rfl; exact ha.ne_top.symm

/--
lemma `IsCoatom.ne_top_iff_eq` / 引理 `IsCoatom.ne_top_iff_eq`

English:
lemma IsCoatom.ne_top_iff_eq
  given: (ha : IsCoatom a) (hab : a <= b)
  statement: b != ⊤ ↔ b = a
  proof: (ha.ne_iff_eq_top hab).not_right.symm

中文:
引理 IsCoatom.ne_top_iff_eq
  条件: (ha : IsCoatom a) (hab : a <= b)
  结论: b != ⊤ ↔ b = a
  证明: (ha.ne_iff_eq_top hab).not_right.symm

Depends on / 依赖: ha.ne_iff_eq_top, ne_iff_eq_top, not_right, not_right.symm
-/
lemma IsCoatom.ne_top_iff_eq (ha : IsCoatom a) (hab : a <= b) : b != ⊤ ↔ b = a :=
  (ha.ne_iff_eq_top hab).not_right.symm

/--
theorem `IsCoatom.Ici_eq` / 定理 `IsCoatom.Ici_eq`

English:
theorem IsCoatom.Ici_eq
  given: (h : IsCoatom a)
  statement: Set.Ici a = {⊤, a}
  proof: h.dual.Iic_eq

中文:
定理 IsCoatom.Ici_eq
  条件: (h : IsCoatom a)
  结论: 集合.左闭右无界区间 a = {⊤, a}
  证明: h.dual.Iic_eq

Depends on / 依赖: Iic_eq, h.dual.Iic_eq
-/
theorem IsCoatom.Ici_eq (h : IsCoatom a) : Set.Ici a = {⊤, a} :=
  h.dual.Iic_eq

/--
lemma `Set.Ioi_eq_singleton_top_iff` / 引理 `Set.Ioi_eq_singleton_top_iff`

English:
lemma Set.Ioi_eq_singleton_top_iff
  statement: Ioi a = {⊤} ↔ IsCoatom a
  proof: by
  simp [IsCoatom, superset_antisymm_iff, lt_top_iff_ne_top]

@[simp]

中文:
引理 集合.Ioi_eq_singleton_top_iff
  结论: 左开右无界区间 a = {⊤} ↔ IsCoatom a
  证明: by
  simp [IsCoatom, superset_antisymm_iff, lt_top_iff_ne_top]

@[simp]

Depends on / 依赖: IsCoatom, lt_top_iff_ne_top, superset_antisymm_iff
-/
lemma Set.Ioi_eq_singleton_top_iff : Ioi a = {⊤} ↔ IsCoatom a := by
  simp [IsCoatom, superset_antisymm_iff, lt_top_iff_ne_top]

@[simp]
/--
theorem `covBy_top_iff` / 定理 `covBy_top_iff`

English:
theorem covBy_top_iff
  statement: a ⋖ ⊤ ↔ IsCoatom a
  proof: toDual_covBy_toDual_iff.symm.trans bot_covBy_iff

alias ⟨CovBy.isCoatom, IsCoatom.covBy_top⟩ := covBy_top_iff

中文:
定理 covBy_top_iff
  结论: a ⋖ ⊤ ↔ IsCoatom a
  证明: toDual_covBy_toDual_iff.symm.trans bot_covBy_iff

alias ⟨CovBy.isCoatom, IsCoatom.covBy_top⟩ := covBy_top_iff

Depends on / 依赖: bot_covBy_iff, toDual_covBy_toDual_iff, toDual_covBy_toDual_iff.symm.trans
-/
theorem covBy_top_iff : a ⋖ ⊤ ↔ IsCoatom a :=
  toDual_covBy_toDual_iff.symm.trans bot_covBy_iff

alias ⟨CovBy.isCoatom, IsCoatom.covBy_top⟩ := covBy_top_iff

namespace SetLike

variable {A B : Type*} [PartialOrder A] [SetLike A B] [IsConcreteLE A B]

/--
theorem `isAtom_iff` / 定理 `isAtom_iff`

English:
theorem isAtom_iff
  given: [OrderBot A] {K : A}
  proof: by
  simp_rw [IsAtom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ <= _), and_imp, exists_imp, ← and_imp, and_comm]

中文:
定理 isAtom_iff
  条件: [有底序 A] {K : A}
  证明: by
  simp_rw [IsAtom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ <= _), and_imp, exists_imp, ← and_imp, and_comm]

Depends on / 依赖: IsAtom, SetLike, SetLike.not_le_iff_exists, and_comm, and_imp, exists_imp, lt_iff_le_not_ge, not_le_iff_exists, simp_rw
-/
theorem isAtom_iff [OrderBot A] {K : A} :
    IsAtom K ↔ K != ⊥ ∧ forall H g, H <= K -> g ∉ H -> g in K -> H = ⊥ := by
  simp_rw [IsAtom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ <= _), and_imp, exists_imp, ← and_imp, and_comm]

/--
theorem `isCoatom_iff` / 定理 `isCoatom_iff`

English:
theorem isCoatom_iff
  given: [OrderTop A] {K : A}
  proof: by
  simp_rw [IsCoatom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ <= _), and_imp, exists_imp, ← and_imp, and_comm]

中文:
定理 isCoatom_iff
  条件: [有顶序 A] {K : A}
  证明: by
  simp_rw [IsCoatom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ <= _), and_imp, exists_imp, ← and_imp, and_comm]

Depends on / 依赖: IsCoatom, SetLike, SetLike.not_le_iff_exists, and_comm, and_imp, exists_imp, lt_iff_le_not_ge, not_le_iff_exists, simp_rw
-/
theorem isCoatom_iff [OrderTop A] {K : A} :
    IsCoatom K ↔ K != ⊤ ∧ forall H g, K <= H -> g ∉ K -> g in H -> H = ⊤ := by
  simp_rw [IsCoatom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ <= _), and_imp, exists_imp, ← and_imp, and_comm]

/--
theorem `covBy_iff` / 定理 `covBy_iff`

English:
theorem covBy_iff
  given: {K L : A}
  proof: by
  refine and_congr_right fun _ => forall_congr' fun H => ?_
  contrapose!
  rw [lt_iff_le_not_ge]; rw [lt_iff_le_and_ne]; rw [and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, and_comm, implies_true]

中文:
定理 covBy_iff
  条件: {K L : A}
  证明: by
  refine and_congr_right fun _ => forall_congr' fun H => ?_
  contrapose!
  rw [lt_iff_le_not_ge]; rw [lt_iff_le_and_ne]; rw [and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, and_comm, implies_true]

Depends on / 依赖: SetLike, SetLike.not_le_iff_exists, and_and_and_comm, and_assoc, and_comm, and_congr_right, and_congr_right_iff, contrapose, exists_and_left, forall_congr, implies_true, lt_iff_le_and_ne, lt_iff_le_not_ge, not_le_iff_exists, simp_rw
-/
theorem covBy_iff {K L : A} :
    K ⋖ L ↔ K < L ∧ forall H g, K <= H -> H <= L -> g ∉ K -> g in H -> H = L := by
  refine and_congr_right fun _ => forall_congr' fun H => ?_
  contrapose!
  rw [lt_iff_le_not_ge]; rw [lt_iff_le_and_ne]; rw [and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, and_comm, implies_true]

/--
theorem `covBy_iff'` / 定理 `covBy_iff'`

English:
theorem covBy_iff'
  given: {K L : A}
  proof: by
  refine and_congr_right fun _ => forall_congr' fun H => not_iff_not.mp ?_
  push Not
  rw [lt_iff_le_and_ne]; rw [lt_iff_le_not_ge]; rw [and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, ne_comm, implies_true]

中文:
定理 covBy_iff'
  条件: {K L : A}
  证明: by
  refine and_congr_right fun _ => forall_congr' fun H => not_iff_not.mp ?_
  push Not
  rw [lt_iff_le_and_ne]; rw [lt_iff_le_not_ge]; rw [and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, ne_comm, implies_true]

Depends on / 依赖: SetLike, SetLike.not_le_iff_exists, and_and_and_comm, and_assoc, and_comm, and_congr_right, and_congr_right_iff, exists_and_left, forall_congr, implies_true, lt_iff_le_and_ne, lt_iff_le_not_ge, ne_comm, not_iff_not, not_iff_not.mp, not_le_iff_exists, simp_rw
-/
theorem covBy_iff' {K L : A} :
    K ⋖ L ↔ K < L ∧ forall H g, K <= H -> H <= L -> g ∉ H -> g in L -> H = K := by
  refine and_congr_right fun _ => forall_congr' fun H => not_iff_not.mp ?_
  push Not
  rw [lt_iff_le_and_ne]; rw [lt_iff_le_not_ge]; rw [and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, ne_comm, implies_true]

end SetLike

end PartialOrder

section Coframe
variable [Coframe α] {f : ι -> α} {s : Set α} {a : α}

/--
lemma `IsCoatom.iInf_le` / 引理 `IsCoatom.iInf_le`

English:
lemma IsCoatom.iInf_le
  given: (ha : IsCoatom a)
  statement: iInf f <= a ↔ exists i, f i <= a
  proof: IsAtom.le_iSup (α := αᵒᵈ) ha

中文:
引理 IsCoatom.iInf_le
  条件: (ha : IsCoatom a)
  结论: iInf f <= a ↔ 存在 i, f i <= a
  证明: IsAtom.le_iSup (α := αᵒᵈ) ha
-/
protected lemma IsCoatom.iInf_le (ha : IsCoatom a) : iInf f <= a ↔ exists i, f i <= a :=
  IsAtom.le_iSup (α := αᵒᵈ) ha

/--
lemma `IsCoatom.sInf_le` / 引理 `IsCoatom.sInf_le`

English:
lemma IsCoatom.sInf_le
  given: (ha : IsCoatom a)
  statement: sInf s <= a ↔ exists b in s, b <= a
  proof: by
  simp [sInf_eq_iInf', ha.iInf_le]

中文:
引理 IsCoatom.sInf_le
  条件: (ha : IsCoatom a)
  结论: sInf s <= a ↔ 存在 b in s, b <= a
  证明: by
  simp [sInf_eq_iInf', ha.iInf_le]
-/
protected lemma IsCoatom.sInf_le (ha : IsCoatom a) : sInf s <= a ↔ exists b in s, b <= a := by
  simp [sInf_eq_iInf', ha.iInf_le]

end Coframe
end IsCoatom

section PartialOrder

variable [PartialOrder α] {a b : α}

@[simp]
/--
theorem `Set.Ici.isAtom_iff` / 定理 `Set.Ici.isAtom_iff`

English:
theorem Set.Ici.isAtom_iff
  given: {b : Set.Ici a}
  statement: IsAtom b ↔ a ⋖ b
  proof: by
  rw [← bot_covBy_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => a <= c) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Ici

@[simp]

中文:
定理 集合.左闭右无界区间.isAtom_iff
  条件: {b : 集合.左闭右无界区间 a}
  结论: IsAtom b ↔ a ⋖ b
  证明: by
  rw [← bot_covBy_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => a <= c) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Ici

@[simp]

Depends on / 依赖: OrdConnected, OrderEmbedding, OrderEmbedding.coe_subtype, OrderEmbedding.subtype, Set.OrdConnected.apply_covBy_apply_iff, Set.ordConnected_Ici, Subtype, Subtype.range_coe_subtype, apply_covBy_apply_iff, bot_covBy_iff, coe_subtype, ordConnected_Ici, range_coe_subtype, subtype
-/
theorem Set.Ici.isAtom_iff {b : Set.Ici a} : IsAtom b ↔ a ⋖ b := by
  rw [← bot_covBy_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => a <= c) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Ici

@[simp]
/--
theorem `Set.Iic.isCoatom_iff` / 定理 `Set.Iic.isCoatom_iff`

English:
theorem Set.Iic.isCoatom_iff
  given: {a : Set.Iic b}
  statement: IsCoatom a ↔ ↑a ⋖ b
  proof: by
  rw [← covBy_top_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => c <= b) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Iic

中文:
定理 集合.左无界右闭区间.isCoatom_iff
  条件: {a : 集合.左无界右闭区间 b}
  结论: IsCoatom a ↔ ↑a ⋖ b
  证明: by
  rw [← covBy_top_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => c <= b) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Iic

Depends on / 依赖: However, OrdConnected, OrderEmbedding, OrderEmbedding.coe_subtype, OrderEmbedding.subtype, Set.OrdConnected.apply_covBy_apply_iff, Set.ordConnected_Iic, Subtype, Subtype.range_coe_subtype, apply_covBy_apply_iff, coe_subtype, covBy_top_iff, fst.rnDeriv, function, functions, measurable, ordConnected_Iic, range_coe_subtype, restrict, rnDeriv
-/
theorem Set.Iic.isCoatom_iff {a : Set.Iic b} : IsCoatom a ↔ ↑a ⋖ b := by
  rw [← covBy_top_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => c <= b) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using! Set.ordConnected_Iic

/--
theorem `covBy_iff_atom_Ici` / 定理 `covBy_iff_atom_Ici`

English:
theorem covBy_iff_atom_Ici
  given: (h : a <= b)
  statement: a ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici a)
  proof: by simp

中文:
定理 covBy_iff_atom_Ici
  条件: (h : a <= b)
  结论: a ⋖ b ↔ IsAtom (⟨b, h⟩ : 集合.左闭右无界区间 a)
  证明: by simp
-/
theorem covBy_iff_atom_Ici (h : a <= b) : a ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici a) := by simp

/--
theorem `covBy_iff_coatom_Iic` / 定理 `covBy_iff_coatom_Iic`

English:
theorem covBy_iff_coatom_Iic
  given: (h : a <= b)
  statement: a ⋖ b ↔ IsCoatom (⟨a, h⟩ : Set.Iic b)
  proof: by simp

中文:
定理 covBy_iff_coatom_Iic
  条件: (h : a <= b)
  结论: a ⋖ b ↔ IsCoatom (⟨a, h⟩ : 集合.左无界右闭区间 b)
  证明: by simp
-/
theorem covBy_iff_coatom_Iic (h : a <= b) : a ⋖ b ↔ IsCoatom (⟨a, h⟩ : Set.Iic b) := by simp

end PartialOrder

section SemilatticeInf
variable [SemilatticeInf α] [OrderBot α] {a b : α}

/--
lemma `IsAtom.not_disjoint_iff_le` / 引理 `IsAtom.not_disjoint_iff_le`

English:
lemma IsAtom.not_disjoint_iff_le
  given: (ha : IsAtom a)
  statement: ¬ Disjoint a b ↔ a <= b
  proof: by
  rw [disjoint_iff]; rw [← inf_eq_left]; exact ha.ne_bot_iff_eq inf_le_left

中文:
引理 IsAtom.not_disjoint_iff_le
  条件: (ha : IsAtom a)
  结论: ¬ Disjoint a b ↔ a <= b
  证明: by
  rw [disjoint_iff]; rw [← inf_eq_left]; exact ha.ne_bot_iff_eq inf_le_left

Depends on / 依赖: disjoint_iff, ha.ne_bot_iff_eq, inf_eq_left, inf_le_left, ne_bot_iff_eq
-/
lemma IsAtom.not_disjoint_iff_le (ha : IsAtom a) : ¬ Disjoint a b ↔ a <= b := by
  rw [disjoint_iff]; rw [← inf_eq_left]; exact ha.ne_bot_iff_eq inf_le_left

/--
lemma `IsAtom.not_le_iff_disjoint` / 引理 `IsAtom.not_le_iff_disjoint`

English:
lemma IsAtom.not_le_iff_disjoint
  given: (ha : IsAtom a)
  statement: ¬ a <= b ↔ Disjoint a b
  proof: ha.not_disjoint_iff_le.not_right.symm

中文:
引理 IsAtom.not_le_iff_disjoint
  条件: (ha : IsAtom a)
  结论: ¬ a <= b ↔ Disjoint a b
  证明: ha.not_disjoint_iff_le.not_right.symm

Depends on / 依赖: ha.not_disjoint_iff_le.not_right.symm, not_disjoint_iff_le, not_right
-/
lemma IsAtom.not_le_iff_disjoint (ha : IsAtom a) : ¬ a <= b ↔ Disjoint a b :=
  ha.not_disjoint_iff_le.not_right.symm

/--
lemma `IsAtom.disjoint_of_ne` / 引理 `IsAtom.disjoint_of_ne`

English:
lemma IsAtom.disjoint_of_ne
  given: (ha : IsAtom a) (hb : IsAtom b) (hab : a != b)
  statement: Disjoint a b
  proof: by
  simp [← ha.not_le_iff_disjoint, hb.le_iff, hab, ha.ne_bot]

中文:
引理 IsAtom.disjoint_of_ne
  条件: (ha : IsAtom a) (hb : IsAtom b) (hab : a != b)
  结论: Disjoint a b
  证明: by
  simp [← ha.not_le_iff_disjoint, hb.le_iff, hab, ha.ne_bot]

Depends on / 依赖: ha.ne_bot, ha.not_le_iff_disjoint, hb.le_iff, le_iff, ne_bot, not_le_iff_disjoint
-/
lemma IsAtom.disjoint_of_ne (ha : IsAtom a) (hb : IsAtom b) (hab : a != b) : Disjoint a b := by
  simp [← ha.not_le_iff_disjoint, hb.le_iff, hab, ha.ne_bot]

end SemilatticeInf

section SemilatticeSup
variable [SemilatticeSup α] [OrderTop α] {a b : α}

/--
lemma `IsCoatom.not_codisjoint_iff_le` / 引理 `IsCoatom.not_codisjoint_iff_le`

English:
lemma IsCoatom.not_codisjoint_iff_le
  given: (ha : IsCoatom a)
  statement: ¬ Codisjoint a b ↔ b <= a
  proof: by
  rw [codisjoint_iff]; rw [← sup_eq_left]; exact ha.ne_top_iff_eq le_sup_left

中文:
引理 IsCoatom.not_codisjoint_iff_le
  条件: (ha : IsCoatom a)
  结论: ¬ Codisjoint a b ↔ b <= a
  证明: by
  rw [codisjoint_iff]; rw [← sup_eq_left]; exact ha.ne_top_iff_eq le_sup_left

Depends on / 依赖: codisjoint_iff, ha.ne_top_iff_eq, le_sup_left, ne_top_iff_eq, sup_eq_left
-/
lemma IsCoatom.not_codisjoint_iff_le (ha : IsCoatom a) : ¬ Codisjoint a b ↔ b <= a := by
  rw [codisjoint_iff]; rw [← sup_eq_left]; exact ha.ne_top_iff_eq le_sup_left

/--
lemma `IsCoatom.not_le_iff_codisjoint` / 引理 `IsCoatom.not_le_iff_codisjoint`

English:
lemma IsCoatom.not_le_iff_codisjoint
  given: (ha : IsCoatom a)
  statement: ¬ b <= a ↔ Codisjoint a b
  proof: ha.not_codisjoint_iff_le.not_right.symm

中文:
引理 IsCoatom.not_le_iff_codisjoint
  条件: (ha : IsCoatom a)
  结论: ¬ b <= a ↔ Codisjoint a b
  证明: ha.not_codisjoint_iff_le.not_right.symm

Depends on / 依赖: ha.not_codisjoint_iff_le.not_right.symm, not_codisjoint_iff_le, not_right
-/
lemma IsCoatom.not_le_iff_codisjoint (ha : IsCoatom a) : ¬ b <= a ↔ Codisjoint a b :=
  ha.not_codisjoint_iff_le.not_right.symm

/--
lemma `IsCoatom.codisjoint_of_ne` / 引理 `IsCoatom.codisjoint_of_ne`

English:
lemma IsCoatom.codisjoint_of_ne
  given: (ha : IsCoatom a) (hb : IsCoatom b) (hab : a != b)
  proof: by
  simp [← ha.not_le_iff_codisjoint, hb.le_iff, hab, ha.ne_top]

中文:
引理 IsCoatom.codisjoint_of_ne
  条件: (ha : IsCoatom a) (hb : IsCoatom b) (hab : a != b)
  证明: by
  simp [← ha.not_le_iff_codisjoint, hb.le_iff, hab, ha.ne_top]

Depends on / 依赖: ha.ne_top, ha.not_le_iff_codisjoint, hb.le_iff, le_iff, ne_top, not_le_iff_codisjoint
-/
lemma IsCoatom.codisjoint_of_ne (ha : IsCoatom a) (hb : IsCoatom b) (hab : a != b) :
    Codisjoint a b := by
  simp [← ha.not_le_iff_codisjoint, hb.le_iff, hab, ha.ne_top]

/--
theorem `IsCoatom.sup_eq_top_of_ne` / 定理 `IsCoatom.sup_eq_top_of_ne`

English:
theorem IsCoatom.sup_eq_top_of_ne
  given: (ha : IsCoatom a) (hb : IsCoatom b) (hab : a != b)
  statement: a ⊔ b = ⊤
  proof: codisjoint_iff.1 ha.codisjoint_of_ne hb hab

中文:
定理 IsCoatom.sup_eq_top_of_ne
  条件: (ha : IsCoatom a) (hb : IsCoatom b) (hab : a != b)
  结论: a ⊔ b = ⊤
  证明: codisjoint_iff.1 ha.codisjoint_of_ne hb hab

Depends on / 依赖: codisjoint_iff, codisjoint_of_ne, ha.codisjoint_of_ne
-/
theorem IsCoatom.sup_eq_top_of_ne (ha : IsCoatom a) (hb : IsCoatom b) (hab : a != b) : a ⊔ b = ⊤ :=
codisjoint_iff.1 ha.codisjoint_of_ne hb hab

end SemilatticeSup

end Atoms

section Atomic

variable [PartialOrder α] (α)

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
@[mk_iff]
/--
Definition of `IsAtomic` / `IsAtomic` 的定义

English:
class IsAtomic
  parameters: [OrderBot α]
  axioms and operations (1):
    - eq_bot_or_exists_atom_le : forall b : α, b = ⊥ ∨ exists a : α, IsAtom a ∧ a <= b

中文:
类 是原子的
  参数: [有底序 α]
  公理与运算 (1 个):
    - eq_bot_or_exists_atom_le : 对任意 b : α, b = ⊥ ∨ 存在 a : α, IsAtom a ∧ a <= b
-/
class IsAtomic [OrderBot α] : Prop where
  /-- Every element other than `⊥` has an atom below it. -/
  eq_bot_or_exists_atom_le : forall b : α, b = ⊥ ∨ exists a : α, IsAtom a ∧ a <= b

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
@[mk_iff]
/--
Definition of `IsCoatomic` / `IsCoatomic` 的定义

English:
class IsCoatomic
  parameters: [OrderTop α]
  axioms and operations (1):
    - eq_top_or_exists_le_coatom : forall b : α, b = ⊤ ∨ exists a : α, IsCoatom a ∧ b <= a

中文:
类 是余原子的
  参数: [有顶序 α]
  公理与运算 (1 个):
    - eq_top_or_exists_le_coatom : 对任意 b : α, b = ⊤ ∨ 存在 a : α, IsCoatom a ∧ b <= a
-/
class IsCoatomic [OrderTop α] : Prop where
  /-- Every element other than `⊤` has an atom above it. -/
  eq_top_or_exists_le_coatom : forall b : α, b = ⊤ ∨ exists a : α, IsCoatom a ∧ b <= a

export IsAtomic (eq_bot_or_exists_atom_le)

export IsCoatomic (eq_top_or_exists_le_coatom)

/--
lemma `IsAtomic.exists_atom` / 引理 `IsAtomic.exists_atom`

English:
lemma IsAtomic.exists_atom
  given: [OrderBot α] [Nontrivial α] [IsAtomic α]
  statement: exists a : α, IsAtom a
  proof: have ⟨b, hb⟩ := exists_ne (⊥ : α)
  have ⟨a, ha⟩ := (eq_bot_or_exists_atom_le b).resolve_left hb
  ⟨a, ha.1⟩

中文:
引理 是原子的.存在_atom
  条件: [有底序 α] [非平凡 α] [是原子的 α]
  结论: 存在 a : α, IsAtom a
  证明: have ⟨b, hb⟩ := exists_ne (⊥ : α)
  have ⟨a, ha⟩ := (eq_bot_or_exists_atom_le b).resolve_left hb
  ⟨a, ha.1⟩

Depends on / 依赖: eq_bot_or_exists_atom_le, exists_ne, resolve_left
-/
lemma IsAtomic.exists_atom [OrderBot α] [Nontrivial α] [IsAtomic α] : exists a : α, IsAtom a :=
  have ⟨b, hb⟩ := exists_ne (⊥ : α)
  have ⟨a, ha⟩ := (eq_bot_or_exists_atom_le b).resolve_left hb
  ⟨a, ha.1⟩

/--
lemma `IsCoatomic.exists_coatom` / 引理 `IsCoatomic.exists_coatom`

English:
lemma IsCoatomic.exists_coatom
  given: [OrderTop α] [Nontrivial α] [IsCoatomic α]
  statement: exists a : α, IsCoatom a
  proof: have ⟨b, hb⟩ := exists_ne (⊤ : α)
  have ⟨a, ha⟩ := (eq_top_or_exists_le_coatom b).resolve_left hb
  ⟨a, ha.1⟩

中文:
引理 是余原子的.存在_coatom
  条件: [有顶序 α] [非平凡 α] [是余原子的 α]
  结论: 存在 a : α, IsCoatom a
  证明: have ⟨b, hb⟩ := exists_ne (⊤ : α)
  have ⟨a, ha⟩ := (eq_top_or_exists_le_coatom b).resolve_left hb
  ⟨a, ha.1⟩

Depends on / 依赖: eq_top_or_exists_le_coatom, exists_ne, resolve_left
-/
lemma IsCoatomic.exists_coatom [OrderTop α] [Nontrivial α] [IsCoatomic α] : exists a : α, IsCoatom a :=
  have ⟨b, hb⟩ := exists_ne (⊤ : α)
  have ⟨a, ha⟩ := (eq_top_or_exists_le_coatom b).resolve_left hb
  ⟨a, ha.1⟩

variable {α}

@[simp]
/--
theorem `isCoatomic_dual_iff_isAtomic` / 定理 `isCoatomic_dual_iff_isAtomic`

English:
theorem isCoatomic_dual_iff_isAtomic
  given: [OrderBot α]
  statement: IsCoatomic αᵒᵈ ↔ IsAtomic α
  proof: ⟨fun h => ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩, fun h =>
    ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩⟩

@[simp]

中文:
定理 isCoatomic_dual_iff_isAtomic
  条件: [有底序 α]
  结论: 是余原子的 αᵒᵈ ↔ 是原子的 α
  证明: ⟨fun h => ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩, fun h =>
    ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩⟩

@[simp]

Depends on / 依赖: eq_bot_or_exists_atom_le, eq_top_or_exists_le_coatom, h.eq_bot_or_exists_atom_le, h.eq_top_or_exists_le_coatom
-/
theorem isCoatomic_dual_iff_isAtomic [OrderBot α] : IsCoatomic αᵒᵈ ↔ IsAtomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩, fun h =>
    ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩⟩

@[simp]
/--
theorem `isAtomic_dual_iff_isCoatomic` / 定理 `isAtomic_dual_iff_isCoatomic`

English:
theorem isAtomic_dual_iff_isCoatomic
  given: [OrderTop α]
  statement: IsAtomic αᵒᵈ ↔ IsCoatomic α
  proof: ⟨fun h => ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩, fun h =>
    ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩⟩

中文:
定理 isAtomic_dual_iff_isCoatomic
  条件: [有顶序 α]
  结论: 是原子的 αᵒᵈ ↔ 是余原子的 α
  证明: ⟨fun h => ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩, fun h =>
    ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩⟩

Depends on / 依赖: eq_bot_or_exists_atom_le, eq_top_or_exists_le_coatom, h.eq_bot_or_exists_atom_le, h.eq_top_or_exists_le_coatom
-/
theorem isAtomic_dual_iff_isCoatomic [OrderTop α] : IsAtomic αᵒᵈ ↔ IsCoatomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩, fun h =>
    ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩⟩

namespace IsAtomic

variable [OrderBot α] [IsAtomic α]

/--
Instance `_root_.OrderDual.instIsCoatomic` / 实例 `_root_.OrderDual.instIsCoatomic`

English:
instance _root_.OrderDual.instIsCoatomic
  signature: : IsCoatomic αᵒᵈ
  body: isCoatomic_dual_iff_isAtomic.2 ‹IsAtomic α›

中文:
实例 _root_.OrderDual.instIsCoatomic
  签名: : 是余原子的 αᵒᵈ
  定义体: isCoatomic_dual_iff_isAtomic.2 ‹IsAtomic α›

Depends on / 依赖: IsAtomic, isCoatomic_dual_iff_isAtomic
-/
instance _root_.OrderDual.instIsCoatomic : IsCoatomic αᵒᵈ :=
  isCoatomic_dual_iff_isAtomic.2 ‹IsAtomic α›

/--
Instance `Set.Iic.isAtomic` / 实例 `Set.Iic.isAtomic`

English:
instance Set.Iic.isAtomic
  signature: {x : α}
  body: ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩⟩

中文:
实例 集合.左无界右闭区间.isAtomic
  签名: {x : α}
  定义体: ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩⟩

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, eq_bot_or_exists_atom_le, ha.Iic, hay.trans, mk_eq_mk
-/
instance Set.Iic.isAtomic {x : α} : IsAtomic (Set.Iic x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩⟩

end IsAtomic

namespace IsCoatomic

variable [OrderTop α] [IsCoatomic α]

/--
Instance `_root_.OrderDual.instIsAtomic` / 实例 `_root_.OrderDual.instIsAtomic`

English:
instance _root_.OrderDual.instIsAtomic
  signature: : IsAtomic αᵒᵈ
  body: isAtomic_dual_iff_isCoatomic.2 ‹IsCoatomic α›

中文:
实例 _root_.OrderDual.instIsAtomic
  签名: : 是原子的 αᵒᵈ
  定义体: isAtomic_dual_iff_isCoatomic.2 ‹IsCoatomic α›

Depends on / 依赖: IsCoatomic, isAtomic_dual_iff_isCoatomic
-/
instance _root_.OrderDual.instIsAtomic : IsAtomic αᵒᵈ :=
  isAtomic_dual_iff_isCoatomic.2 ‹IsCoatomic α›

/--
Instance `Set.Ici.isCoatomic` / 实例 `Set.Ici.isCoatomic`

English:
instance Set.Ici.isCoatomic
  signature: {x : α}
  body: ⟨fun ⟨y, hy⟩ =>
    (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, le_trans hy hay⟩, ha.Ici (le_trans hy hay), hay⟩⟩

中文:
实例 集合.左闭右无界区间.isCoatomic
  签名: {x : α}
  定义体: ⟨fun ⟨y, hy⟩ =>
    (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, le_trans hy hay⟩, ha.Ici (le_trans hy hay), hay⟩⟩

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, eq_top_or_exists_le_coatom, ha.Ici, le_trans, mk_eq_mk
-/
instance Set.Ici.isCoatomic {x : α} : IsCoatomic (Set.Ici x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, le_trans hy hay⟩, ha.Ici (le_trans hy hay), hay⟩⟩

end IsCoatomic

/--
theorem `isAtomic_iff_forall_isAtomic_Iic` / 定理 `isAtomic_iff_forall_isAtomic_Iic`

English:
theorem isAtomic_iff_forall_isAtomic_Iic
  given: [OrderBot α]
  proof: ⟨@IsAtomic.Set.Iic.isAtomic _ _ _, fun h =>
    ⟨fun x =>
      ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
        (Exists.imp' (↑) fun ⟨_, _⟩ => And.imp_left IsAtom.of_isAtom_coe_Iic)⟩⟩

中文:
定理 isAtomic_iff_对任意_isAtomic_Iic
  条件: [有底序 α]
  证明: ⟨@IsAtomic.Set.Iic.isAtomic _ _ _, fun h =>
    ⟨fun x =>
      ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
        (Exists.imp' (↑) fun ⟨_, _⟩ => And.imp_left IsAtom.of_isAtom_coe_Iic)⟩⟩

Depends on / 依赖: And.imp_left, Exists, Exists.imp, IsAtom, IsAtom.of_isAtom_coe_Iic, IsAtomic, IsAtomic.Set.Iic.isAtomic, Set.Iic, Subtype, Subtype.mk_eq_mk, eq_bot_or_exists_atom_le, imp_left, isAtomic, mk_eq_mk, of_isAtom_coe_Iic
-/
theorem isAtomic_iff_forall_isAtomic_Iic [OrderBot α] :
    IsAtomic α ↔ forall x : α, IsAtomic (Set.Iic x) :=
  ⟨@IsAtomic.Set.Iic.isAtomic _ _ _, fun h =>
    ⟨fun x =>
      ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
        (Exists.imp' (↑) fun ⟨_, _⟩ => And.imp_left IsAtom.of_isAtom_coe_Iic)⟩⟩

/--
theorem `isCoatomic_iff_forall_isCoatomic_Ici` / 定理 `isCoatomic_iff_forall_isCoatomic_Ici`

English:
theorem isCoatomic_iff_forall_isCoatomic_Ici
  given: [OrderTop α]
  proof: isAtomic_dual_iff_isCoatomic.symm.trans
isAtomic_iff_forall_isAtomic_Iic.trans
      forall_congr' fun _ => isCoatomic_dual_iff_isAtomic.symm.trans Iff.rfl

中文:
定理 isCoatomic_iff_对任意_isCoatomic_Ici
  条件: [有顶序 α]
  证明: isAtomic_dual_iff_isCoatomic.symm.trans
isAtomic_iff_forall_isAtomic_Iic.trans
      forall_congr' fun _ => isCoatomic_dual_iff_isAtomic.symm.trans Iff.rfl

Depends on / 依赖: Iff.rfl, forall_congr, isAtomic_dual_iff_isCoatomic, isAtomic_dual_iff_isCoatomic.symm.trans, isAtomic_iff_forall_isAtomic_Iic, isAtomic_iff_forall_isAtomic_Iic.trans, isCoatomic_dual_iff_isAtomic, isCoatomic_dual_iff_isAtomic.symm.trans
-/
theorem isCoatomic_iff_forall_isCoatomic_Ici [OrderTop α] :
    IsCoatomic α ↔ forall x : α, IsCoatomic (Set.Ici x) :=
isAtomic_dual_iff_isCoatomic.symm.trans
isAtomic_iff_forall_isAtomic_Iic.trans
      forall_congr' fun _ => isCoatomic_dual_iff_isAtomic.symm.trans Iff.rfl

section StronglyAtomic

variable {α : Type*} {a b : α} [Preorder α]

/-- An order is strongly atomic if every nontrivial interval `[a, b]`
contains an element covering `a`. -/
@[mk_iff]
/--
Definition of `IsStronglyAtomic` / `IsStronglyAtomic` 的定义

English:
class IsStronglyAtomic
  parameters: (α : Type*) [Preorder α]
  axioms and operations (1):
    - exists_covBy_le_of_lt : forall (a b : α), a < b -> exists x, a ⋖ x ∧ x <= b

中文:
类 是StronglyAtomic
  参数: (α : 类型) [预序 α]
  公理与运算 (1 个):
    - exists_covBy_le_of_lt : 对任意 (a b : α), a < b -> 存在 x, a ⋖ x ∧ x <= b
-/
class IsStronglyAtomic (α : Type*) [Preorder α] : Prop where
  exists_covBy_le_of_lt : forall (a b : α), a < b -> exists x, a ⋖ x ∧ x <= b

/--
theorem `exists_covBy_le_of_lt` / 定理 `exists_covBy_le_of_lt`

English:
theorem exists_covBy_le_of_lt
  given: [IsStronglyAtomic α] (h : a < b)
  statement: exists x, a ⋖ x ∧ x <= b
  proof: IsStronglyAtomic.exists_covBy_le_of_lt a b h

alias LT.lt.exists_covby_le := exists_covBy_le_of_lt

中文:
定理 存在_covBy_le_of_lt
  条件: [是StronglyAtomic α] (h : a < b)
  结论: 存在 x, a ⋖ x ∧ x <= b
  证明: IsStronglyAtomic.exists_covBy_le_of_lt a b h

alias LT.lt.exists_covby_le := exists_covBy_le_of_lt

Depends on / 依赖: IsStronglyAtomic, IsStronglyAtomic.exists_covBy_le_of_lt, exists_covBy_le_of_lt
-/
theorem exists_covBy_le_of_lt [IsStronglyAtomic α] (h : a < b) : exists x, a ⋖ x ∧ x <= b :=
  IsStronglyAtomic.exists_covBy_le_of_lt a b h

alias LT.lt.exists_covby_le := exists_covBy_le_of_lt

/-- An order is strongly coatomic if every nontrivial interval `[a, b]`
contains an element covered by `b`. -/
@[mk_iff]
/--
Definition of `IsStronglyCoatomic` / `IsStronglyCoatomic` 的定义

English:
class IsStronglyCoatomic
  parameters: (α : Type*) [Preorder α]
  axioms and operations (1):
    - (exists_le_covBy_of_lt : forall (a b : α), a < b -> exists x, a <= x ∧ x ⋖ b)

中文:
类 是StronglyCoatomic
  参数: (α : 类型) [预序 α]
  公理与运算 (1 个):
    - (exists_le_covBy_of_lt : 对任意 (a b : α), a < b -> 存在 x, a <= x ∧ x ⋖ b)
-/
class IsStronglyCoatomic (α : Type*) [Preorder α] : Prop where
  (exists_le_covBy_of_lt : forall (a b : α), a < b -> exists x, a <= x ∧ x ⋖ b)

/--
theorem `exists_le_covBy_of_lt` / 定理 `exists_le_covBy_of_lt`

English:
theorem exists_le_covBy_of_lt
  given: [IsStronglyCoatomic α] (h : a < b)
  statement: exists x, a <= x ∧ x ⋖ b
  proof: IsStronglyCoatomic.exists_le_covBy_of_lt a b h

alias LT.lt.exists_le_covby := exists_le_covBy_of_lt

中文:
定理 存在_le_covBy_of_lt
  条件: [是StronglyCoatomic α] (h : a < b)
  结论: 存在 x, a <= x ∧ x ⋖ b
  证明: IsStronglyCoatomic.exists_le_covBy_of_lt a b h

alias LT.lt.exists_le_covby := exists_le_covBy_of_lt

Depends on / 依赖: IsStronglyCoatomic, IsStronglyCoatomic.exists_le_covBy_of_lt, exists_le_covBy_of_lt
-/
theorem exists_le_covBy_of_lt [IsStronglyCoatomic α] (h : a < b) : exists x, a <= x ∧ x ⋖ b :=
  IsStronglyCoatomic.exists_le_covBy_of_lt a b h

alias LT.lt.exists_le_covby := exists_le_covBy_of_lt

/--
theorem `isStronglyAtomic_dual_iff_is_stronglyCoatomic` / 定理 `isStronglyAtomic_dual_iff_is_stronglyCoatomic`

English:
theorem isStronglyAtomic_dual_iff_is_stronglyCoatomic
  proof: by
  simpa [isStronglyAtomic_iff, OrderDual.exists, OrderDual.forall,
    OrderDual.toDual_le_toDual, and_comm, isStronglyCoatomic_iff] using forall_comm

中文:
定理 isStronglyAtomic_dual_iff_is_stronglyCoatomic
  证明: by
  simpa [isStronglyAtomic_iff, OrderDual.exists, OrderDual.forall,
    OrderDual.toDual_le_toDual, and_comm, isStronglyCoatomic_iff] using forall_comm

Depends on / 依赖: OrderDual, OrderDual.exists, OrderDual.forall, OrderDual.toDual_le_toDual, and_comm, forall_comm, isStronglyAtomic_iff, isStronglyCoatomic_iff, toDual_le_toDual
-/
theorem isStronglyAtomic_dual_iff_is_stronglyCoatomic :
    IsStronglyAtomic αᵒᵈ ↔ IsStronglyCoatomic α := by
  simpa [isStronglyAtomic_iff, OrderDual.exists, OrderDual.forall,
    OrderDual.toDual_le_toDual, and_comm, isStronglyCoatomic_iff] using forall_comm

/--
theorem `isStronglyCoatomic_dual_iff_is_stronglyAtomic` / 定理 `isStronglyCoatomic_dual_iff_is_stronglyAtomic`

English:
theorem isStronglyCoatomic_dual_iff_is_stronglyAtomic
  proof: by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; rfl

中文:
定理 isStronglyCoatomic_dual_iff_is_stronglyAtomic
  证明: by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; rfl
-/
@[simp] theorem isStronglyCoatomic_dual_iff_is_stronglyAtomic :
    IsStronglyCoatomic αᵒᵈ ↔ IsStronglyAtomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; rfl

/--
Instance `OrderDual.instIsStronglyCoatomic` / 实例 `OrderDual.instIsStronglyCoatomic`

English:
instance OrderDual.instIsStronglyCoatomic
  signature: [IsStronglyAtomic α]
  body: by
  rwa [isStronglyCoatomic_dual_iff_is_stronglyAtomic]

中文:
实例 OrderDual.instIsStronglyCoatomic
  签名: [是StronglyAtomic α]
  定义体: by
  rwa [isStronglyCoatomic_dual_iff_is_stronglyAtomic]

Depends on / 依赖: isStronglyCoatomic_dual_iff_is_stronglyAtomic
-/
instance OrderDual.instIsStronglyCoatomic [IsStronglyAtomic α] : IsStronglyCoatomic αᵒᵈ := by
  rwa [isStronglyCoatomic_dual_iff_is_stronglyAtomic]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStronglyCoatomic
  signature: α] : IsStronglyAtomic αᵒᵈ
  body: by
  rwa [isStronglyAtomic_dual_iff_is_stronglyCoatomic]

中文:
实例 [是StronglyCoatomic
  签名: α] : 是StronglyAtomic αᵒᵈ
  定义体: by
  rwa [isStronglyAtomic_dual_iff_is_stronglyCoatomic]

Depends on / 依赖: isStronglyAtomic_dual_iff_is_stronglyCoatomic
-/
instance [IsStronglyCoatomic α] : IsStronglyAtomic αᵒᵈ := by
  rwa [isStronglyAtomic_dual_iff_is_stronglyCoatomic]

/--
Instance `IsStronglyAtomic.isAtomic` / 实例 `IsStronglyAtomic.isAtomic`

English:
instance IsStronglyAtomic.isAtomic
  signature: (α : Type*) [PartialOrder α] [OrderBot α] [IsStronglyAtomic α]
  body: by
    rw [or_iff_not_imp_left]; rw [← Ne]; rw [← bot_lt_iff_ne_bot]
    refine fun hlt => ?_
    obtain ⟨x, hx, hxa⟩ := hlt.exists_covby_le
    exact ⟨x, bot_covBy_iff.1 hx, hxa⟩

中文:
实例 是StronglyAtomic.isAtomic
  签名: (α : 类型) [偏序 α] [有底序 α] [是StronglyAtomic α]
  定义体: by
    rw [or_iff_not_imp_left]; rw [← Ne]; rw [← bot_lt_iff_ne_bot]
    refine fun hlt => ?_
    obtain ⟨x, hx, hxa⟩ := hlt.exists_covby_le
    exact ⟨x, bot_covBy_iff.1 hx, hxa⟩

Depends on / 依赖: bot_covBy_iff, bot_lt_iff_ne_bot, exists_covby_le, hlt.exists_covby_le, or_iff_not_imp_left
-/
instance IsStronglyAtomic.isAtomic (α : Type*) [PartialOrder α] [OrderBot α] [IsStronglyAtomic α] :
    IsAtomic α where
  eq_bot_or_exists_atom_le a := by
    rw [or_iff_not_imp_left]; rw [← Ne]; rw [← bot_lt_iff_ne_bot]
    refine fun hlt => ?_
    obtain ⟨x, hx, hxa⟩ := hlt.exists_covby_le
    exact ⟨x, bot_covBy_iff.1 hx, hxa⟩

/--
Instance `IsStronglyCoatomic.toIsCoatomic` / 实例 `IsStronglyCoatomic.toIsCoatomic`

English:
instance IsStronglyCoatomic.toIsCoatomic
  signature: (α : Type*) [PartialOrder α] [OrderTop α]
  body: isAtomic_dual_iff_isCoatomic.1 IsStronglyAtomic.isAtomic (α := αᵒᵈ)

中文:
实例 是StronglyCoatomic.toIsCoatomic
  签名: (α : 类型) [偏序 α] [有顶序 α]
  定义体: isAtomic_dual_iff_isCoatomic.1 IsStronglyAtomic.isAtomic (α := αᵒᵈ)

Depends on / 依赖: IsStronglyAtomic, IsStronglyAtomic.isAtomic, isAtomic, isAtomic_dual_iff_isCoatomic
-/
instance IsStronglyCoatomic.toIsCoatomic (α : Type*) [PartialOrder α] [OrderTop α]
    [IsStronglyCoatomic α] : IsCoatomic α :=
isAtomic_dual_iff_isCoatomic.1 IsStronglyAtomic.isAtomic (α := αᵒᵈ)

/--
theorem `Set.OrdConnected.isStronglyAtomic` / 定理 `Set.OrdConnected.isStronglyAtomic`

English:
theorem Set.OrdConnected.isStronglyAtomic
  statement: [IsStronglyAtomic α] {s : Set α}
  proof: by
    rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
    obtain ⟨x, hcx, hxd⟩ := (Subtype.mk_lt_mk.1 hcd).exists_covby_le
    exact ⟨⟨x, h.out' hc hd ⟨hcx.le, hxd⟩⟩,
      ⟨by simpa
        using! hcx.lt, fun y hy hy' => hcx.2 (by simpa using! hy) (by simpa using! hy')⟩, hxd⟩

中文:
定理 集合.序连通.isStronglyAtomic
  结论: [是StronglyAtomic α] {s : 集合 α}
  证明: by
    rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
    obtain ⟨x, hcx, hxd⟩ := (Subtype.mk_lt_mk.1 hcd).exists_covby_le
    exact ⟨⟨x, h.out' hc hd ⟨hcx.le, hxd⟩⟩,
      ⟨by simpa
        using! hcx.lt, fun y hy hy' => hcx.2 (by simpa using! hy) (by simpa using! hy')⟩, hxd⟩

Depends on / 依赖: Subtype, Subtype.mk_lt_mk, exists_covby_le, h.out, hcx.le, hcx.lt, mk_lt_mk
-/
theorem Set.OrdConnected.isStronglyAtomic [IsStronglyAtomic α] {s : Set α}
    (h : Set.OrdConnected s) : IsStronglyAtomic s where
  exists_covBy_le_of_lt := by
    rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
    obtain ⟨x, hcx, hxd⟩ := (Subtype.mk_lt_mk.1 hcd).exists_covby_le
    exact ⟨⟨x, h.out' hc hd ⟨hcx.le, hxd⟩⟩,
      ⟨by simpa
        using! hcx.lt, fun y hy hy' => hcx.2 (by simpa using! hy) (by simpa using! hy')⟩, hxd⟩

/--
theorem `Set.OrdConnected.isStronglyCoatomic` / 定理 `Set.OrdConnected.isStronglyCoatomic`

English:
theorem Set.OrdConnected.isStronglyCoatomic
  statement: [IsStronglyCoatomic α] {s : Set α}
  proof: isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 h.dual.isStronglyAtomic

中文:
定理 集合.序连通.isStronglyCoatomic
  结论: [是StronglyCoatomic α] {s : 集合 α}
  证明: isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 h.dual.isStronglyAtomic

Depends on / 依赖: h.dual.isStronglyAtomic, isStronglyAtomic, isStronglyAtomic_dual_iff_is_stronglyCoatomic
-/
theorem Set.OrdConnected.isStronglyCoatomic [IsStronglyCoatomic α] {s : Set α}
    (h : Set.OrdConnected s) : IsStronglyCoatomic s :=
  isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 h.dual.isStronglyAtomic

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStronglyAtomic
  signature: α] {s
  body: Set.OrdConnected.isStronglyAtomic by assumption

中文:
实例 [是StronglyAtomic
  签名: α] {s
  定义体: Set.OrdConnected.isStronglyAtomic by assumption

Depends on / 依赖: OrdConnected, Set.OrdConnected.isStronglyAtomic, isStronglyAtomic
-/
instance [IsStronglyAtomic α] {s : Set α} [Set.OrdConnected s] : IsStronglyAtomic s :=
Set.OrdConnected.isStronglyAtomic by assumption

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStronglyCoatomic
  signature: α] {s
  body: Set.OrdConnected.isStronglyCoatomic by assumption

中文:
实例 [是StronglyCoatomic
  签名: α] {s
  定义体: Set.OrdConnected.isStronglyCoatomic by assumption

Depends on / 依赖: OrdConnected, Set.OrdConnected.isStronglyCoatomic, isStronglyCoatomic
-/
instance [IsStronglyCoatomic α] {s : Set α} [h : Set.OrdConnected s] : IsStronglyCoatomic s :=
Set.OrdConnected.isStronglyCoatomic by assumption

/--
Instance `SuccOrder.toIsStronglyAtomic` / 实例 `SuccOrder.toIsStronglyAtomic`

English:
instance SuccOrder.toIsStronglyAtomic
  signature: [SuccOrder α]
  body: ⟨SuccOrder.succ a, Order.covBy_succ_of_not_isMax fun ha => ha.not_lt hab,
      SuccOrder.succ_le_of_lt hab⟩

中文:
实例 Succ序.toIsStronglyAtomic
  签名: [Succ序 α]
  定义体: ⟨SuccOrder.succ a, Order.covBy_succ_of_not_isMax fun ha => ha.not_lt hab,
      SuccOrder.succ_le_of_lt hab⟩

Depends on / 依赖: Order.covBy_succ_of_not_isMax, SuccOrder, SuccOrder.succ, SuccOrder.succ_le_of_lt, covBy_succ_of_not_isMax, ha.not_lt, not_lt, succ_le_of_lt
-/
instance SuccOrder.toIsStronglyAtomic [SuccOrder α] : IsStronglyAtomic α where
  exists_covBy_le_of_lt a _ hab :=
    ⟨SuccOrder.succ a, Order.covBy_succ_of_not_isMax fun ha => ha.not_lt hab,
      SuccOrder.succ_le_of_lt hab⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PredOrder
  signature: α] : IsStronglyCoatomic α
  body: by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

中文:
实例 [Pred序
  签名: α] : 是StronglyCoatomic α
  定义体: by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

Depends on / 依赖: infer_instance, isStronglyAtomic_dual_iff_is_stronglyCoatomic
-/
instance [PredOrder α] : IsStronglyCoatomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

end StronglyAtomic

section WellFounded

/--
theorem `IsStronglyAtomic.of_wellFounded_lt` / 定理 `IsStronglyAtomic.of_wellFounded_lt`

English:
theorem IsStronglyAtomic.of_wellFounded_lt
  given: (h : WellFounded ((· < ·) : α -> α -> Prop))
  proof: by
    refine ⟨WellFounded.min h (Set.Ioc a b) ⟨b, hab,rfl.le⟩, ?_⟩
    have hmem := (WellFounded.min_mem h (Set.Ioc a b) ⟨b, hab,rfl.le⟩)
    exact ⟨⟨hmem.1,fun c hac hlt => WellFounded.not_lt_min h
      (Set.Ioc a b) ⟨hac, hlt.le.trans hmem.2⟩ hlt⟩, hmem.2⟩

中文:
定理 是StronglyAtomic.of_wellFounded_lt
  条件: (h : 良基 ((· < ·) : α -> α -> 命题))
  证明: by
    refine ⟨WellFounded.min h (Set.Ioc a b) ⟨b, hab,rfl.le⟩, ?_⟩
    have hmem := (WellFounded.min_mem h (Set.Ioc a b) ⟨b, hab,rfl.le⟩)
    exact ⟨⟨hmem.1,fun c hac hlt => WellFounded.not_lt_min h
      (Set.Ioc a b) ⟨hac, hlt.le.trans hmem.2⟩ hlt⟩, hmem.2⟩

Depends on / 依赖: Set.Ioc, WellFounded, WellFounded.min, WellFounded.min_mem, WellFounded.not_lt_min, hlt.le.trans, min_mem, not_lt_min, rfl.le
-/
theorem IsStronglyAtomic.of_wellFounded_lt (h : WellFounded ((· < ·) : α -> α -> Prop)) :
    IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    refine ⟨WellFounded.min h (Set.Ioc a b) ⟨b, hab,rfl.le⟩, ?_⟩
    have hmem := (WellFounded.min_mem h (Set.Ioc a b) ⟨b, hab,rfl.le⟩)
    exact ⟨⟨hmem.1,fun c hac hlt => WellFounded.not_lt_min h
      (Set.Ioc a b) ⟨hac, hlt.le.trans hmem.2⟩ hlt⟩, hmem.2⟩

/--
theorem `IsStronglyCoatomic.of_wellFounded_gt` / 定理 `IsStronglyCoatomic.of_wellFounded_gt`

English:
theorem IsStronglyCoatomic.of_wellFounded_gt
  given: (h : WellFounded ((· > ·) : α -> α -> Prop))
  proof: isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 IsStronglyAtomic.of_wellFounded_lt (α := αᵒᵈ) h

中文:
定理 是StronglyCoatomic.of_wellFounded_gt
  条件: (h : 良基 ((· > ·) : α -> α -> 命题))
  证明: isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 IsStronglyAtomic.of_wellFounded_lt (α := αᵒᵈ) h

Depends on / 依赖: IsStronglyAtomic, IsStronglyAtomic.of_wellFounded_lt, isStronglyAtomic_dual_iff_is_stronglyCoatomic, of_wellFounded_lt
-/
theorem IsStronglyCoatomic.of_wellFounded_gt (h : WellFounded ((· > ·) : α -> α -> Prop)) :
    IsStronglyCoatomic α :=
isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 IsStronglyAtomic.of_wellFounded_lt (α := αᵒᵈ) h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WellFoundedLT
  signature: α] : IsStronglyAtomic α
  body: IsStronglyAtomic.of_wellFounded_lt wellFounded_lt

中文:
实例 [WellFoundedLT
  签名: α] : 是StronglyAtomic α
  定义体: IsStronglyAtomic.of_wellFounded_lt wellFounded_lt

Depends on / 依赖: IsStronglyAtomic, IsStronglyAtomic.of_wellFounded_lt, of_wellFounded_lt, wellFounded_lt
-/
instance [WellFoundedLT α] : IsStronglyAtomic α :=
  IsStronglyAtomic.of_wellFounded_lt wellFounded_lt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WellFoundedGT
  signature: α] : IsStronglyCoatomic α
  body: IsStronglyCoatomic.of_wellFounded_gt wellFounded_gt

中文:
实例 [WellFoundedGT
  签名: α] : 是StronglyCoatomic α
  定义体: IsStronglyCoatomic.of_wellFounded_gt wellFounded_gt

Depends on / 依赖: IsStronglyCoatomic, IsStronglyCoatomic.of_wellFounded_gt, of_wellFounded_gt, wellFounded_gt
-/
instance [WellFoundedGT α] : IsStronglyCoatomic α :=
    IsStronglyCoatomic.of_wellFounded_gt wellFounded_gt

/--
theorem `isAtomic_of_orderBot_wellFounded_lt` / 定理 `isAtomic_of_orderBot_wellFounded_lt`

English:
theorem isAtomic_of_orderBot_wellFounded_lt
  statement: [OrderBot α]
  proof: (IsStronglyAtomic.of_wellFounded_lt h).isAtomic

中文:
定理 isAtomic_of_orderBot_wellFounded_lt
  结论: [有底序 α]
  证明: (IsStronglyAtomic.of_wellFounded_lt h).isAtomic

Depends on / 依赖: IsStronglyAtomic, IsStronglyAtomic.of_wellFounded_lt, isAtomic, of_wellFounded_lt
-/
theorem isAtomic_of_orderBot_wellFounded_lt [OrderBot α]
    (h : WellFounded ((· < ·) : α -> α -> Prop)) : IsAtomic α :=
  (IsStronglyAtomic.of_wellFounded_lt h).isAtomic

/--
theorem `isCoatomic_of_orderTop_gt_wellFounded` / 定理 `isCoatomic_of_orderTop_gt_wellFounded`

English:
theorem isCoatomic_of_orderTop_gt_wellFounded
  statement: [OrderTop α]
  proof: isAtomic_dual_iff_isCoatomic.1 (@isAtomic_of_orderBot_wellFounded_lt αᵒᵈ _ _ h)

中文:
定理 isCoatomic_of_orderTop_gt_wellFounded
  结论: [有顶序 α]
  证明: isAtomic_dual_iff_isCoatomic.1 (@isAtomic_of_orderBot_wellFounded_lt αᵒᵈ _ _ h)

Depends on / 依赖: isAtomic_dual_iff_isCoatomic, isAtomic_of_orderBot_wellFounded_lt
-/
theorem isCoatomic_of_orderTop_gt_wellFounded [OrderTop α]
    (h : WellFounded ((· > ·) : α -> α -> Prop)) : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 (@isAtomic_of_orderBot_wellFounded_lt αᵒᵈ _ _ h)

end WellFounded

namespace BooleanAlgebra

/--
theorem `le_iff_atom_le_imp` / 定理 `le_iff_atom_le_imp`

English:
theorem le_iff_atom_le_imp
  given: {α} [BooleanAlgebra α] [IsAtomic α] {x y : α}
  proof: by
  refine ⟨fun h a _ => (le_trans · h), fun h => ?_⟩
  have : x ⊓ yᶜ = ⊥ := of_not_not fun hbot =>
    have ⟨a, ha, hle⟩ := (eq_bot_or_exists_atom_le _).resolve_left hbot
    have ⟨hx, hy'⟩ := le_inf_iff.1 hle
    have hy := h a ha hx
    have : a <= y ⊓ yᶜ := le_inf_iff.2 ⟨hy, hy'⟩
    ha.1 (by simpa using this)
  exact (eq_compl_iff_isCompl.1 (by simp)).inf_right_eq_bot_iff.1 this

中文:
定理 le_iff_atom_le_imp
  条件: {α} [布尔代数 α] [是原子的 α] {x y : α}
  证明: by
  refine ⟨fun h a _ => (le_trans · h), fun h => ?_⟩
  have : x ⊓ yᶜ = ⊥ := of_not_not fun hbot =>
    have ⟨a, ha, hle⟩ := (eq_bot_or_exists_atom_le _).resolve_left hbot
    have ⟨hx, hy'⟩ := le_inf_iff.1 hle
    have hy := h a ha hx
    have : a <= y ⊓ yᶜ := le_inf_iff.2 ⟨hy, hy'⟩
    ha.1 (by simpa using this)
  exact (eq_compl_iff_isCompl.1 (by simp)).inf_right_eq_bot_iff.1 this

Depends on / 依赖: eq_bot_or_exists_atom_le, eq_compl_iff_isCompl, inf_right_eq_bot_iff, le_inf_iff, le_trans, of_not_not, resolve_left
-/
theorem le_iff_atom_le_imp {α} [BooleanAlgebra α] [IsAtomic α] {x y : α} :
    x <= y ↔ forall a, IsAtom a -> a <= x -> a <= y := by
  refine ⟨fun h a _ => (le_trans · h), fun h => ?_⟩
  have : x ⊓ yᶜ = ⊥ := of_not_not fun hbot =>
    have ⟨a, ha, hle⟩ := (eq_bot_or_exists_atom_le _).resolve_left hbot
    have ⟨hx, hy'⟩ := le_inf_iff.1 hle
    have hy := h a ha hx
    have : a <= y ⊓ yᶜ := le_inf_iff.2 ⟨hy, hy'⟩
    ha.1 (by simpa using this)
  exact (eq_compl_iff_isCompl.1 (by simp)).inf_right_eq_bot_iff.1 this

/--
theorem `eq_iff_atom_le_iff` / 定理 `eq_iff_atom_le_iff`

English:
theorem eq_iff_atom_le_iff
  given: {α} [BooleanAlgebra α] [IsAtomic α] {x y : α}
  proof: by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  exact le_antisymm (le_iff_atom_le_imp.2 fun a ha hx => (h a ha).1 hx)
    (le_iff_atom_le_imp.2 fun a ha hy => (h a ha).2 hy)

中文:
定理 eq_iff_atom_le_iff
  条件: {α} [布尔代数 α] [是原子的 α] {x y : α}
  证明: by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  exact le_antisymm (le_iff_atom_le_imp.2 fun a ha hx => (h a ha).1 hx)
    (le_iff_atom_le_imp.2 fun a ha hy => (h a ha).2 hy)

Depends on / 依赖: le_antisymm, le_iff_atom_le_imp
-/
theorem eq_iff_atom_le_iff {α} [BooleanAlgebra α] [IsAtomic α] {x y : α} :
    x = y ↔ forall a, IsAtom a -> (a <= x ↔ a <= y) := by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  exact le_antisymm (le_iff_atom_le_imp.2 fun a ha hx => (h a ha).1 hx)
    (le_iff_atom_le_imp.2 fun a ha hy => (h a ha).2 hy)

end BooleanAlgebra

namespace CompleteBooleanAlgebra

-- See note [reducible non-instances]
/--
Definition of `toCompleteAtomicBooleanAlgebra` / `toCompleteAtomicBooleanAlgebra` 的定义

English:
abbreviation toCompleteAtomicBooleanAlgebra
  signature: {α} [CompleteBooleanAlgebra α] [IsAtomic α]
  body: ‹CompleteBooleanAlgebra α›
  iInf_iSup_eq f := BooleanAlgebra.eq_iff_atom_le_iff.2 fun a ha => by
    simp only [le_iInf_iff, ha.le_iSup, Classical.skolem]

中文:
缩写 toCompleteAtomic布尔eanAlgebra
  签名: {α} [完备布尔代数 α] [是原子的 α]
  定义体: ‹CompleteBooleanAlgebra α›
  iInf_iSup_eq f := BooleanAlgebra.eq_iff_atom_le_iff.2 fun a ha => by
    simp only [le_iInf_iff, ha.le_iSup, Classical.skolem]

Depends on / 依赖: CompleteBooleanAlgebra
-/
abbrev toCompleteAtomicBooleanAlgebra {α} [CompleteBooleanAlgebra α] [IsAtomic α] :
    CompleteAtomicBooleanAlgebra α where
  __ := ‹CompleteBooleanAlgebra α›
  iInf_iSup_eq f := BooleanAlgebra.eq_iff_atom_le_iff.2 fun a ha => by
    simp only [le_iInf_iff, ha.le_iSup, Classical.skolem]

end CompleteBooleanAlgebra

end Atomic

section Atomistic

variable (α) [PartialOrder α]

/-- A lattice is atomistic iff every element is a `sSup` of a set of atoms. -/
@[mk_iff]
/--
Definition of `IsAtomistic` / `IsAtomistic` 的定义

English:
class IsAtomistic
  parameters: [OrderBot α]
  axioms and operations (1):
    - isLUB_atoms : forall b : α, exists s : Set α, IsLUB s b ∧ forall a, a in s -> IsAtom a

中文:
类 是Atomistic
  参数: [有底序 α]
  公理与运算 (1 个):
    - isLUB_atoms : 对任意 b : α, 存在 s : 集合 α, IsLUB s b ∧ 对任意 a, a in s -> IsAtom a
-/
class IsAtomistic [OrderBot α] : Prop where
  /-- Every element is a `sSup` of a set of atoms. -/
  isLUB_atoms : forall b : α, exists s : Set α, IsLUB s b ∧ forall a, a in s -> IsAtom a

/-- A lattice is coatomistic iff every element is an `sInf` of a set of coatoms. -/
@[mk_iff]
/--
Definition of `IsCoatomistic` / `IsCoatomistic` 的定义

English:
class IsCoatomistic
  parameters: [OrderTop α]
  axioms and operations (1):
    - isGLB_coatoms : forall b : α, exists s : Set α, IsGLB s b ∧ forall a, a in s -> IsCoatom a

中文:
类 是余atomistic
  参数: [有顶序 α]
  公理与运算 (1 个):
    - isGLB_coatoms : 对任意 b : α, 存在 s : 集合 α, IsGLB s b ∧ 对任意 a, a in s -> IsCoatom a
-/
class IsCoatomistic [OrderTop α] : Prop where
  /-- Every element is a `sInf` of a set of coatoms. -/
  isGLB_coatoms : forall b : α, exists s : Set α, IsGLB s b ∧ forall a, a in s -> IsCoatom a

export IsAtomistic (isLUB_atoms)

export IsCoatomistic (isGLB_coatoms)

variable {α}

@[simp]
/--
theorem `isCoatomistic_dual_iff_isAtomistic` / 定理 `isCoatomistic_dual_iff_isAtomistic`

English:
theorem isCoatomistic_dual_iff_isAtomistic
  given: [OrderBot α]
  statement: IsCoatomistic αᵒᵈ ↔ IsAtomistic α
  proof: ⟨fun h => ⟨fun b => by apply h.isGLB_coatoms⟩, fun h => ⟨fun b => by apply h.isLUB_atoms⟩⟩

@[simp]

中文:
定理 isCoatomistic_dual_iff_isAtomistic
  条件: [有底序 α]
  结论: 是余atomistic αᵒᵈ ↔ 是Atomistic α
  证明: ⟨fun h => ⟨fun b => by apply h.isGLB_coatoms⟩, fun h => ⟨fun b => by apply h.isLUB_atoms⟩⟩

@[simp]

Depends on / 依赖: h.isGLB_coatoms, h.isLUB_atoms, isGLB_coatoms, isLUB_atoms
-/
theorem isCoatomistic_dual_iff_isAtomistic [OrderBot α] : IsCoatomistic αᵒᵈ ↔ IsAtomistic α :=
  ⟨fun h => ⟨fun b => by apply h.isGLB_coatoms⟩, fun h => ⟨fun b => by apply h.isLUB_atoms⟩⟩

@[simp]
/--
theorem `isAtomistic_dual_iff_isCoatomistic` / 定理 `isAtomistic_dual_iff_isCoatomistic`

English:
theorem isAtomistic_dual_iff_isCoatomistic
  given: [OrderTop α]
  statement: IsAtomistic αᵒᵈ ↔ IsCoatomistic α
  proof: ⟨fun h => ⟨fun b => by apply h.isLUB_atoms⟩, fun h => ⟨fun b => by apply h.isGLB_coatoms⟩⟩

中文:
定理 isAtomistic_dual_iff_isCoatomistic
  条件: [有顶序 α]
  结论: 是Atomistic αᵒᵈ ↔ 是余atomistic α
  证明: ⟨fun h => ⟨fun b => by apply h.isLUB_atoms⟩, fun h => ⟨fun b => by apply h.isGLB_coatoms⟩⟩

Depends on / 依赖: h.isGLB_coatoms, h.isLUB_atoms, isGLB_coatoms, isLUB_atoms
-/
theorem isAtomistic_dual_iff_isCoatomistic [OrderTop α] : IsAtomistic αᵒᵈ ↔ IsCoatomistic α :=
  ⟨fun h => ⟨fun b => by apply h.isLUB_atoms⟩, fun h => ⟨fun b => by apply h.isGLB_coatoms⟩⟩

namespace IsAtomistic

/--
Instance `_root_.OrderDual.instIsCoatomistic` / 实例 `_root_.OrderDual.instIsCoatomistic`

English:
instance _root_.OrderDual.instIsCoatomistic
  signature: [OrderBot α] [h : IsAtomistic α]
  body: isCoatomistic_dual_iff_isAtomistic.2 h

中文:
实例 _root_.OrderDual.instIsCoatomistic
  签名: [有底序 α] [h : 是Atomistic α]
  定义体: isCoatomistic_dual_iff_isAtomistic.2 h

Depends on / 依赖: isCoatomistic_dual_iff_isAtomistic
-/
instance _root_.OrderDual.instIsCoatomistic [OrderBot α] [h : IsAtomistic α] : IsCoatomistic αᵒᵈ :=
  isCoatomistic_dual_iff_isAtomistic.2 h

variable [OrderBot α] [IsAtomistic α]

instance (priority := 100) : IsAtomic α :=
  ⟨fun b => by
    rcases isLUB_atoms b with ⟨s, hsb, hs⟩
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp_all
    · exact Or.inr ⟨a, hs _ ha, hsb.1 ha⟩⟩

end IsAtomistic

section IsAtomistic

variable [OrderBot α] [IsAtomistic α]

/--
theorem `isLUB_atoms_le` / 定理 `isLUB_atoms_le`

English:
theorem isLUB_atoms_le
  given: (b : α)
  statement: IsLUB { a : α | IsAtom a ∧ a <= b } b
  proof: by
  rcases isLUB_atoms b with ⟨s, hsb, hs⟩
  exact ⟨fun c hc => hc.2, fun c hc => hsb.2 fun i hi => hc ⟨hs _ hi, hsb.1 hi⟩⟩

中文:
定理 isLUB_atoms_le
  条件: (b : α)
  结论: IsLUB { a : α | IsAtom a ∧ a <= b } b
  证明: by
  rcases isLUB_atoms b with ⟨s, hsb, hs⟩
  exact ⟨fun c hc => hc.2, fun c hc => hsb.2 fun i hi => hc ⟨hs _ hi, hsb.1 hi⟩⟩

Depends on / 依赖: isLUB_atoms
-/
theorem isLUB_atoms_le (b : α) : IsLUB { a : α | IsAtom a ∧ a <= b } b := by
  rcases isLUB_atoms b with ⟨s, hsb, hs⟩
  exact ⟨fun c hc => hc.2, fun c hc => hsb.2 fun i hi => hc ⟨hs _ hi, hsb.1 hi⟩⟩

/--
theorem `isLUB_atoms_top` / 定理 `isLUB_atoms_top`

English:
theorem isLUB_atoms_top
  given: [OrderTop α]
  statement: IsLUB { a : α | IsAtom a } ⊤
  proof: by
  simpa using isLUB_atoms_le (⊤ : α)

中文:
定理 isLUB_atoms_top
  条件: [有顶序 α]
  结论: IsLUB { a : α | IsAtom a } ⊤
  证明: by
  simpa using isLUB_atoms_le (⊤ : α)

Depends on / 依赖: isLUB_atoms_le
-/
theorem isLUB_atoms_top [OrderTop α] : IsLUB { a : α | IsAtom a } ⊤ := by
  simpa using isLUB_atoms_le (⊤ : α)

/--
theorem `le_iff_atom_le_imp` / 定理 `le_iff_atom_le_imp`

English:
theorem le_iff_atom_le_imp
  given: {a b : α}
  statement: a <= b ↔ forall c : α, IsAtom c -> c <= a -> c <= b
  proof: ⟨fun hab _ _ hca => hca.trans hab,
   fun h => (isLUB_atoms_le a).mono (isLUB_atoms_le b) fun _ ⟨h₁, h₂⟩ => ⟨h₁, h _ h₁ h₂⟩⟩

中文:
定理 le_iff_atom_le_imp
  条件: {a b : α}
  结论: a <= b ↔ 对任意 c : α, IsAtom c -> c <= a -> c <= b
  证明: ⟨fun hab _ _ hca => hca.trans hab,
   fun h => (isLUB_atoms_le a).mono (isLUB_atoms_le b) fun _ ⟨h₁, h₂⟩ => ⟨h₁, h _ h₁ h₂⟩⟩

Depends on / 依赖: hca.trans, isLUB_atoms_le
-/
theorem le_iff_atom_le_imp {a b : α} : a <= b ↔ forall c : α, IsAtom c -> c <= a -> c <= b :=
  ⟨fun hab _ _ hca => hca.trans hab,
   fun h => (isLUB_atoms_le a).mono (isLUB_atoms_le b) fun _ ⟨h₁, h₂⟩ => ⟨h₁, h _ h₁ h₂⟩⟩

/--
theorem `eq_iff_atom_le_iff` / 定理 `eq_iff_atom_le_iff`

English:
theorem eq_iff_atom_le_iff
  given: {a b : α}
  statement: a = b ↔ forall c, IsAtom c -> (c <= a ↔ c <= b)
  proof: by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  rw [le_antisymm_iff]; rw [le_iff_atom_le_imp]; rw [le_iff_atom_le_imp]
  simp_all

中文:
定理 eq_iff_atom_le_iff
  条件: {a b : α}
  结论: a = b ↔ 对任意 c, IsAtom c -> (c <= a ↔ c <= b)
  证明: by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  rw [le_antisymm_iff]; rw [le_iff_atom_le_imp]; rw [le_iff_atom_le_imp]
  simp_all

Depends on / 依赖: le_antisymm_iff, le_iff_atom_le_imp
-/
theorem eq_iff_atom_le_iff {a b : α} : a = b ↔ forall c, IsAtom c -> (c <= a ↔ c <= b) := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  rw [le_antisymm_iff]; rw [le_iff_atom_le_imp]; rw [le_iff_atom_le_imp]
  simp_all

end IsAtomistic

namespace IsCoatomistic

variable [OrderTop α]

/--
Instance `_root_.OrderDual.instIsAtomistic` / 实例 `_root_.OrderDual.instIsAtomistic`

English:
instance _root_.OrderDual.instIsAtomistic
  signature: [h : IsCoatomistic α]
  body: isAtomistic_dual_iff_isCoatomistic.2 h

中文:
实例 _root_.OrderDual.instIsAtomistic
  签名: [h : 是余atomistic α]
  定义体: isAtomistic_dual_iff_isCoatomistic.2 h

Depends on / 依赖: isAtomistic_dual_iff_isCoatomistic
-/
instance _root_.OrderDual.instIsAtomistic [h : IsCoatomistic α] : IsAtomistic αᵒᵈ :=
  isAtomistic_dual_iff_isCoatomistic.2 h

variable [IsCoatomistic α]

instance (priority := 100) : IsCoatomic α :=
  ⟨fun b => by
    rcases isGLB_coatoms b with ⟨s, hsb, hs⟩
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp_all
    · exact Or.inr ⟨a, hs _ ha, hsb.1 ha⟩⟩

end IsCoatomistic

section CompleteLattice

@[simp]
/--
theorem `sSup_atoms_le_eq` / 定理 `sSup_atoms_le_eq`

English:
theorem sSup_atoms_le_eq
  given: {α} [CompleteLattice α] [IsAtomistic α] (b : α)
  proof: (isLUB_atoms_le b).sSup_eq

@[simp]

中文:
定理 sSup_atoms_le_eq
  条件: {α} [完备格 α] [是Atomistic α] (b : α)
  证明: (isLUB_atoms_le b).sSup_eq

@[simp]

Depends on / 依赖: isLUB_atoms_le, sSup_eq
-/
theorem sSup_atoms_le_eq {α} [CompleteLattice α] [IsAtomistic α] (b : α) :
    sSup { a : α | IsAtom a ∧ a <= b } = b :=
  (isLUB_atoms_le b).sSup_eq

@[simp]
/--
theorem `sSup_atoms_eq_top` / 定理 `sSup_atoms_eq_top`

English:
theorem sSup_atoms_eq_top
  given: {α} [CompleteLattice α] [IsAtomistic α]
  proof: isLUB_atoms_top.sSup_eq

nonrec lemma CompleteLattice.isAtomistic_iff {α} [CompleteLattice α] :
    IsAtomistic α ↔ forall b : α, exists s : Set α, b = sSup s ∧ forall a in s, IsAtom a := by
  simp_rw [isAtomistic_iff, isLUB_iff_sSup_eq, eq_comm]

中文:
定理 sSup_atoms_eq_top
  条件: {α} [完备格 α] [是Atomistic α]
  证明: isLUB_atoms_top.sSup_eq

nonrec lemma CompleteLattice.isAtomistic_iff {α} [CompleteLattice α] :
    IsAtomistic α ↔ forall b : α, exists s : Set α, b = sSup s ∧ forall a in s, IsAtom a := by
  simp_rw [isAtomistic_iff, isLUB_iff_sSup_eq, eq_comm]

Depends on / 依赖: isLUB_atoms_top, isLUB_atoms_top.sSup_eq, sSup_eq
-/
theorem sSup_atoms_eq_top {α} [CompleteLattice α] [IsAtomistic α] :
    sSup { a : α | IsAtom a } = ⊤ :=
  isLUB_atoms_top.sSup_eq

nonrec lemma CompleteLattice.isAtomistic_iff {α} [CompleteLattice α] :
    IsAtomistic α ↔ forall b : α, exists s : Set α, b = sSup s ∧ forall a in s, IsAtom a := by
  simp_rw [isAtomistic_iff, isLUB_iff_sSup_eq, eq_comm]

/--
lemma `eq_sSup_atoms` / 引理 `eq_sSup_atoms`

English:
lemma eq_sSup_atoms
  given: {α} [CompleteLattice α] [IsAtomistic α] (b : α)
  proof: CompleteLattice.isAtomistic_iff.1 ‹_› b

nonrec lemma CompleteLattice.isCoatomistic_iff {α} [CompleteLattice α] :
    IsCoatomistic α ↔ forall b : α, exists s : Set α, b = sInf s ∧ forall a in s, IsCoatom a := by
  simp_rw [isCoatomistic_iff, isGLB_iff_sInf_eq, eq_comm]

中文:
引理 eq_sSup_atoms
  条件: {α} [完备格 α] [是Atomistic α] (b : α)
  证明: CompleteLattice.isAtomistic_iff.1 ‹_› b

nonrec lemma CompleteLattice.isCoatomistic_iff {α} [CompleteLattice α] :
    IsCoatomistic α ↔ forall b : α, exists s : Set α, b = sInf s ∧ forall a in s, IsCoatom a := by
  simp_rw [isCoatomistic_iff, isGLB_iff_sInf_eq, eq_comm]

Depends on / 依赖: CompleteLattice, CompleteLattice.isAtomistic_iff, isAtomistic_iff
-/
lemma eq_sSup_atoms {α} [CompleteLattice α] [IsAtomistic α] (b : α) :
    exists s : Set α, b = sSup s ∧ forall a in s, IsAtom a :=
  CompleteLattice.isAtomistic_iff.1 ‹_› b

nonrec lemma CompleteLattice.isCoatomistic_iff {α} [CompleteLattice α] :
    IsCoatomistic α ↔ forall b : α, exists s : Set α, b = sInf s ∧ forall a in s, IsCoatom a := by
  simp_rw [isCoatomistic_iff, isGLB_iff_sInf_eq, eq_comm]

/--
lemma `eq_sInf_coatoms` / 引理 `eq_sInf_coatoms`

English:
lemma eq_sInf_coatoms
  given: {α} [CompleteLattice α] [IsCoatomistic α] (b : α)
  proof: CompleteLattice.isCoatomistic_iff.1 ‹_› b

中文:
引理 eq_sInf_coatoms
  条件: {α} [完备格 α] [是余atomistic α] (b : α)
  证明: CompleteLattice.isCoatomistic_iff.1 ‹_› b

Depends on / 依赖: CompleteLattice, CompleteLattice.isCoatomistic_iff, isCoatomistic_iff
-/
lemma eq_sInf_coatoms {α} [CompleteLattice α] [IsCoatomistic α] (b : α) :
    exists s : Set α, b = sInf s ∧ forall a in s, IsCoatom a :=
  CompleteLattice.isCoatomistic_iff.1 ‹_› b

end CompleteLattice

namespace CompleteAtomicBooleanAlgebra

instance {α} [CompleteAtomicBooleanAlgebra α] : IsAtomistic α :=
  CompleteLattice.isAtomistic_iff.2 fun b => by
    inhabit α
    refine ⟨{ a | IsAtom a ∧ a <= b }, ?_, fun a ha => ha.1⟩
    refine le_antisymm ?_ (sSup_le fun c hc => hc.2)
    have : (⨅ c : α, ⨆ x, b ⊓ cond x c (cᶜ)) = b := by simp [iSup_bool_eq]
    rw [← this]; clear this
    simp_rw [iInf_iSup_eq, iSup_le_iff]; intro g
    if h : (⨅ a, b ⊓ cond (g a) a (aᶜ)) = ⊥ then simp [h] else
    refine le_sSup ⟨⟨h, fun c hc => ?_⟩, le_trans (by rfl) (le_iSup _ g)⟩; clear h
    have := lt_of_lt_of_le hc (le_trans (iInf_le _ c) inf_le_right)
    revert this
    nontriviality α
    cases g c <;> simp

instance {α} [CompleteAtomicBooleanAlgebra α] : IsCoatomistic α :=
  isAtomistic_dual_iff_isCoatomistic.1 inferInstance

/--
lemma `eq_setOfPred_le_sSup_and_isAtom` / 引理 `eq_setOfPred_le_sSup_and_isAtom`

English:
lemma eq_setOfPred_le_sSup_and_isAtom
  statement: {α} [CompleteAtomicBooleanAlgebra α] {S : Set α}
  proof: by
  ext a
  refine ⟨fun h => ⟨le_sSup h, hS a h⟩, fun ⟨hale, hatom⟩ => ?_⟩
  obtain ⟨b, hbS, hba⟩ := (IsAtom.le_sSup hatom).mp hale
  obtain rfl | rfl := (hS b hbS).le_iff.mp hba
  · simpa using hatom.1
  assumption

@[deprecated (since := "2026-07-09")]
alias eq_setOf_le_sSup_and_isAtom := eq_setOfPred_le_sSup_and_isAtom

中文:
引理 eq_setOfPred_le_sSup_and_isAtom
  结论: {α} [余mpleteAtomic布尔ean代数 α] {S : 集合 α}
  证明: by
  ext a
  refine ⟨fun h => ⟨le_sSup h, hS a h⟩, fun ⟨hale, hatom⟩ => ?_⟩
  obtain ⟨b, hbS, hba⟩ := (IsAtom.le_sSup hatom).mp hale
  obtain rfl | rfl := (hS b hbS).le_iff.mp hba
  · simpa using hatom.1
  assumption

@[deprecated (since := "2026-07-09")]
alias eq_setOf_le_sSup_and_isAtom := eq_setOfPred_le_sSup_and_isAtom

Depends on / 依赖: IsAtom, IsAtom.le_sSup, le_iff, le_iff.mp, le_sSup
-/
lemma eq_setOfPred_le_sSup_and_isAtom {α} [CompleteAtomicBooleanAlgebra α] {S : Set α}
    (hS : forall a in S, IsAtom a) : S = {a | a <= sSup S ∧ IsAtom a} := by
  ext a
  refine ⟨fun h => ⟨le_sSup h, hS a h⟩, fun ⟨hale, hatom⟩ => ?_⟩
  obtain ⟨b, hbS, hba⟩ := (IsAtom.le_sSup hatom).mp hale
  obtain rfl | rfl := (hS b hbS).le_iff.mp hba
  · simpa using hatom.1
  assumption

@[deprecated (since := "2026-07-09")]
alias eq_setOf_le_sSup_and_isAtom := eq_setOfPred_le_sSup_and_isAtom

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toSetOfIsAtom` / `toSetOfIsAtom` 的定义

English:
definition toSetOfIsAtom
  signature: {α} [CompleteAtomicBooleanAlgebra α]
  body: {a | a <= A}
  invFun S := sSup (Subtype.val '' S)
  left_inv A := by simp [Subtype.coe_image]
  right_inv S := by
    have h : forall a in Subtype.val '' S, IsAtom a := by
      rintro a ⟨a', ha', rfl⟩
      exact a'.prop
    rw [← Subtype.val_injective.image_injective.eq_iff]; rw [eq_setOfPred_le_sSup_and_isAtom h]
    ext a
    simp
  map_rel_iff' {a b} := by
    simpa using le_iff_atom_le_imp.symm

中文:
定义 toSetOfIsAtom
  签名: {α} [余mpleteAtomic布尔ean代数 α]
  定义体: {a | a <= A}
  invFun S := sSup (Subtype.val '' S)
  left_inv A := by simp [Subtype.coe_image]
  right_inv S := by
    have h : forall a in Subtype.val '' S, IsAtom a := by
      rintro a ⟨a', ha', rfl⟩
      exact a'.prop
    rw [← Subtype.val_injective.image_injective.eq_iff]; rw [eq_setOfPred_le_sSup_and_isAtom h]
    ext a
    simp
  map_rel_iff' {a b} := by
    simpa using le_iff_atom_le_imp.symm
-/
def toSetOfIsAtom {α} [CompleteAtomicBooleanAlgebra α] : α ≃o (Set {a : α // IsAtom a}) where
  toFun A := {a | a <= A}
  invFun S := sSup (Subtype.val '' S)
  left_inv A := by simp [Subtype.coe_image]
  right_inv S := by
    have h : forall a in Subtype.val '' S, IsAtom a := by
      rintro a ⟨a', ha', rfl⟩
      exact a'.prop
    rw [← Subtype.val_injective.image_injective.eq_iff]; rw [eq_setOfPred_le_sSup_and_isAtom h]
    ext a
    simp
  map_rel_iff' {a b} := by
    simpa using le_iff_atom_le_imp.symm

end CompleteAtomicBooleanAlgebra

end Atomistic

/-- An order is simple iff it has exactly two elements, `⊥` and `⊤`. -/
@[mk_iff]
/--
Definition of `IsSimpleOrder` / `IsSimpleOrder` 的定义

English:
class IsSimpleOrder
  parameters: (α : Type*) [LE α] [BoundedOrder α]
  extends: Nontrivial α
  axioms and operations (1):
    - eq_bot_or_eq_top : forall a : α, a = ⊥ ∨ a = ⊤

中文:
类 是单序
  参数: (α : 类型) [LE α] [有界序 α]
  继承: 非平凡 α
  公理与运算 (1 个):
    - eq_bot_or_eq_top : 对任意 a : α, a = ⊥ ∨ a = ⊤
-/
class IsSimpleOrder (α : Type*) [LE α] [BoundedOrder α] : Prop extends Nontrivial α where
  /-- Every element is either `⊥` or `⊤` -/
  eq_bot_or_eq_top : forall a : α, a = ⊥ ∨ a = ⊤

export IsSimpleOrder (eq_bot_or_eq_top)

/--
lemma `IsSimpleOrder.of_forall_eq_top` / 引理 `IsSimpleOrder.of_forall_eq_top`

English:
lemma IsSimpleOrder.of_forall_eq_top
  statement: {α : Type*} [LE α] [BoundedOrder α] [Nontrivial α]
  proof: or_iff_not_imp_left.mpr h a

中文:
引理 是单序.of_对任意_eq_top
  结论: {α : 类型} [LE α] [有界序 α] [非平凡 α]
  证明: or_iff_not_imp_left.mpr h a

Depends on / 依赖: or_iff_not_imp_left, or_iff_not_imp_left.mpr
-/
lemma IsSimpleOrder.of_forall_eq_top {α : Type*} [LE α] [BoundedOrder α] [Nontrivial α]
    (h : forall a : α, a != ⊥ -> a = ⊤) :
    IsSimpleOrder α where
eq_bot_or_eq_top a := or_iff_not_imp_left.mpr h a

/--
theorem `isSimpleOrder_iff_isSimpleOrder_orderDual` / 定理 `isSimpleOrder_iff_isSimpleOrder_orderDual`

English:
theorem isSimpleOrder_iff_isSimpleOrder_orderDual
  given: [LE α] [BoundedOrder α]
  proof: by
  constructor <;> intro i
  · exact
      { eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.ofDual a) : _ ∨ _) }
  · exact
      { exists_pair_ne := @exists_pair_ne αᵒᵈ _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.toDual a)) }

中文:
定理 isSimpleOrder_iff_isSimpleOrder_orderDual
  条件: [LE α] [有界序 α]
  证明: by
  constructor <;> intro i
  · exact
      { eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.ofDual a) : _ ∨ _) }
  · exact
      { exists_pair_ne := @exists_pair_ne αᵒᵈ _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.toDual a)) }

Depends on / 依赖: Or.symm, OrderDual, OrderDual.ofDual, OrderDual.toDual, eq_bot_or_eq_top, exists_pair_ne, ofDual, toDual
-/
theorem isSimpleOrder_iff_isSimpleOrder_orderDual [LE α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsSimpleOrder αᵒᵈ := by
  constructor <;> intro i
  · exact
      { eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.ofDual a) : _ ∨ _) }
  · exact
      { exists_pair_ne := @exists_pair_ne αᵒᵈ _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.toDual a)) }

/--
theorem `IsSimpleOrder.bot_ne_top` / 定理 `IsSimpleOrder.bot_ne_top`

English:
theorem IsSimpleOrder.bot_ne_top
  given: [LE α] [BoundedOrder α] [IsSimpleOrder α]
  statement: (⊥ : α) != (⊤ : α)
  proof: by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;> rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
    first | simpa | simpa using h.symm

中文:
定理 是单序.bot_ne_top
  条件: [LE α] [有界序 α] [是单序 α]
  结论: (⊥ : α) != (⊤ : α)
  证明: by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;> rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
    first | simpa | simpa using h.symm

Depends on / 依赖: eq_bot_or_eq_top, exists_pair_ne, h.symm
-/
theorem IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder α] [IsSimpleOrder α] : (⊥ : α) != (⊤ : α) := by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;> rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
    first | simpa | simpa using h.symm

section IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

/--
Instance `OrderDual.instIsSimpleOrder` / 实例 `OrderDual.instIsSimpleOrder`

English:
instance OrderDual.instIsSimpleOrder
  signature: {α} [LE α] [BoundedOrder α] [IsSimpleOrder α]
  body: isSimpleOrder_iff_isSimpleOrder_orderDual.1 (by infer_instance)

中文:
实例 OrderDual.instIsSimpleOrder
  签名: {α} [LE α] [有界序 α] [是单序 α]
  定义体: isSimpleOrder_iff_isSimpleOrder_orderDual.1 (by infer_instance)

Depends on / 依赖: infer_instance, isSimpleOrder_iff_isSimpleOrder_orderDual
-/
instance OrderDual.instIsSimpleOrder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    IsSimpleOrder αᵒᵈ := isSimpleOrder_iff_isSimpleOrder_orderDual.1 (by infer_instance)

/-- A simple `BoundedOrder` induces a preorder. This is not an instance to prevent loops. -/
@[instance_reducible]
/--
Definition of `IsSimpleOrder.preorder` / `IsSimpleOrder.preorder` 的定义

English:
definition IsSimpleOrder.preorder
  signature: {α} [LE α] [BoundedOrder α] [IsSimpleOrder α]
  body: by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
  le_trans a b c := by
    rcases eq_bot_or_eq_top a with (rfl | rfl)
    · simp
    · rcases eq_bot_or_eq_top b with (rfl | rfl)
      · rcases eq_bot_or_eq_top c with (rfl | rfl) <;> simp
      · simp

中文:
定义 是单序.preorder
  签名: {α} [LE α] [有界序 α] [是单序 α]
  定义体: by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
  le_trans a b c := by
    rcases eq_bot_or_eq_top a with (rfl | rfl)
    · simp
    · rcases eq_bot_or_eq_top b with (rfl | rfl)
      · rcases eq_bot_or_eq_top c with (rfl | rfl) <;> simp
      · simp
-/
protected def IsSimpleOrder.preorder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    Preorder α where
  le_refl a := by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
  le_trans a b c := by
    rcases eq_bot_or_eq_top a with (rfl | rfl)
    · simp
    · rcases eq_bot_or_eq_top b with (rfl | rfl)
      · rcases eq_bot_or_eq_top c with (rfl | rfl) <;> simp
      · simp

/-- A simple partial ordered `BoundedOrder` induces a linear order.
This is not an instance to prevent loops. -/
@[instance_reducible]
/--
Definition of `IsSimpleOrder.linearOrder` / `IsSimpleOrder.linearOrder` 的定义

English:
definition IsSimpleOrder.linearOrder
  signature: [DecidableEq α]
  body: { (inferInstance : PartialOrder α) with
    le_total := fun a b => by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
    -- Note from https://github.com/leanprover-community/mathlib4/issues/23976: do we want this inlined or should this be a separate definition?
    toDecidableLE := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left
              (eq_bot_or_eq_top a) ha)) H))
    toDecidableEq := ‹_› }

中文:
定义 是单序.linearOrder
  签名: [DecidableEq α]
  定义体: { (inferInstance : PartialOrder α) with
    le_total := fun a b => by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
    -- Note from https://github.com/leanprover-community/mathlib4/issues/23976: do we want this inlined or should this be a separate definition?
    toDecidableLE := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left
              (eq_bot_or_eq_top a) ha)) H))
    toDecidableEq := ‹_› }
-/
protected def IsSimpleOrder.linearOrder [DecidableEq α] : LinearOrder α :=
  { (inferInstance : PartialOrder α) with
    le_total := fun a b => by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
    -- Note from https://github.com/leanprover-community/mathlib4/issues/23976: do we want this inlined or should this be a separate definition?
    toDecidableLE := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left
              (eq_bot_or_eq_top a) ha)) H))
    toDecidableEq := ‹_› }

/--
theorem `isAtom_top` / 定理 `isAtom_top`

English:
theorem isAtom_top
  statement: IsAtom (⊤ : α)
  proof: ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩

@[simp]

中文:
定理 isAtom_top
  结论: IsAtom (⊤ : α)
  证明: ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩

@[simp]

Depends on / 依赖: Or.resolve_right, eq_bot_or_eq_top, ne_of_lt, resolve_right, top_ne_bot
-/
theorem isAtom_top : IsAtom (⊤ : α) :=
  ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩

@[simp]
/--
theorem `isAtom_iff_eq_top` / 定理 `isAtom_iff_eq_top`

English:
theorem isAtom_iff_eq_top
  given: {a : α}
  statement: IsAtom a ↔ a = ⊤
  proof: ⟨fun h => (eq_bot_or_eq_top a).resolve_left h.1, (· ▸ isAtom_top)⟩

中文:
定理 isAtom_iff_eq_top
  条件: {a : α}
  结论: IsAtom a ↔ a = ⊤
  证明: ⟨fun h => (eq_bot_or_eq_top a).resolve_left h.1, (· ▸ isAtom_top)⟩

Depends on / 依赖: eq_bot_or_eq_top, isAtom_top, resolve_left
-/
theorem isAtom_iff_eq_top {a : α} : IsAtom a ↔ a = ⊤ :=
  ⟨fun h => (eq_bot_or_eq_top a).resolve_left h.1, (· ▸ isAtom_top)⟩

/--
theorem `isCoatom_bot` / 定理 `isCoatom_bot`

English:
theorem isCoatom_bot
  statement: IsCoatom (⊥ : α)
  proof: isAtom_dual_iff_isCoatom.1 isAtom_top

@[simp]

中文:
定理 isCoatom_bot
  结论: IsCoatom (⊥ : α)
  证明: isAtom_dual_iff_isCoatom.1 isAtom_top

@[simp]

Depends on / 依赖: isAtom_dual_iff_isCoatom, isAtom_top
-/
theorem isCoatom_bot : IsCoatom (⊥ : α) :=
  isAtom_dual_iff_isCoatom.1 isAtom_top

@[simp]
/--
theorem `isCoatom_iff_eq_bot` / 定理 `isCoatom_iff_eq_bot`

English:
theorem isCoatom_iff_eq_bot
  given: {a : α}
  statement: IsCoatom a ↔ a = ⊥
  proof: ⟨fun h => (eq_bot_or_eq_top a).resolve_right h.1, (· ▸ isCoatom_bot)⟩

中文:
定理 isCoatom_iff_eq_bot
  条件: {a : α}
  结论: IsCoatom a ↔ a = ⊥
  证明: ⟨fun h => (eq_bot_or_eq_top a).resolve_right h.1, (· ▸ isCoatom_bot)⟩

Depends on / 依赖: eq_bot_or_eq_top, isCoatom_bot, resolve_right
-/
theorem isCoatom_iff_eq_bot {a : α} : IsCoatom a ↔ a = ⊥ :=
  ⟨fun h => (eq_bot_or_eq_top a).resolve_right h.1, (· ▸ isCoatom_bot)⟩

/--
theorem `bot_covBy_top` / 定理 `bot_covBy_top`

English:
theorem bot_covBy_top
  statement: (⊥ : α) ⋖ ⊤
  proof: isAtom_top.bot_covBy

中文:
定理 bot_covBy_top
  结论: (⊥ : α) ⋖ ⊤
  证明: isAtom_top.bot_covBy

Depends on / 依赖: bot_covBy, isAtom_top, isAtom_top.bot_covBy
-/
theorem bot_covBy_top : (⊥ : α) ⋖ ⊤ :=
  isAtom_top.bot_covBy

end IsSimpleOrder

namespace IsSimpleOrder

section Preorder

variable [Preorder α] [BoundedOrder α] [IsSimpleOrder α] {a b : α} (h : a < b)
include h

/--
theorem `eq_bot_of_lt` / 定理 `eq_bot_of_lt`

English:
theorem eq_bot_of_lt
  statement: a = ⊥
  proof: (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right h.ne_top

中文:
定理 eq_bot_of_lt
  结论: a = ⊥
  证明: (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right h.ne_top

Depends on / 依赖: IsSimpleOrder, IsSimpleOrder.eq_bot_or_eq_top, eq_bot_or_eq_top, h.ne_top, ne_top, resolve_right
-/
theorem eq_bot_of_lt : a = ⊥ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right h.ne_top

/--
theorem `eq_top_of_lt` / 定理 `eq_top_of_lt`

English:
theorem eq_top_of_lt
  statement: b = ⊤
  proof: (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left h.ne_bot

alias _root_.LT.lt.eq_bot := eq_bot_of_lt
alias _root_.LT.lt.eq_top := eq_top_of_lt

中文:
定理 eq_top_of_lt
  结论: b = ⊤
  证明: (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left h.ne_bot

alias _root_.LT.lt.eq_bot := eq_bot_of_lt
alias _root_.LT.lt.eq_top := eq_top_of_lt

Depends on / 依赖: IsSimpleOrder, IsSimpleOrder.eq_bot_or_eq_top, eq_bot_or_eq_top, h.ne_bot, ne_bot, resolve_left
-/
theorem eq_top_of_lt : b = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left h.ne_bot

alias _root_.LT.lt.eq_bot := eq_bot_of_lt
alias _root_.LT.lt.eq_top := eq_top_of_lt
end Preorder

section BoundedOrder

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

/-- A simple partial ordered `BoundedOrder` induces a lattice.
This is not an instance to prevent loops -/
@[instance_reducible]
/--
Definition of `lattice` / `lattice` 的定义

English:
definition lattice
  signature: {α} [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]
  body: @LinearOrder.toLattice α IsSimpleOrder.linearOrder

中文:
定义 lattice
  签名: {α} [DecidableEq α] [偏序 α] [有界序 α] [是单序 α]
  定义体: @LinearOrder.toLattice α IsSimpleOrder.linearOrder
-/
protected def lattice {α} [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] :
    Lattice α :=
  @LinearOrder.toLattice α IsSimpleOrder.linearOrder

/-- A lattice that is a `BoundedOrder` is a distributive lattice.
This is not an instance to prevent loops -/
@[instance_reducible]
/--
Definition of `distribLattice` / `distribLattice` 的定义

English:
definition distribLattice
  signature: : DistribLattice α
  body: { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }

中文:
定义 distribLattice
  签名: : Distrib格 α
  定义体: { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
-/
protected def distribLattice : DistribLattice α :=
  { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }

-- see Note [lower instance priority]
instance (priority := 100) : IsAtomic α :=
  ⟨fun b => (eq_bot_or_eq_top b).imp_right fun h => ⟨⊤, ⟨isAtom_top, ge_of_eq h⟩⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 (by infer_instance)

end BoundedOrder

-- It is important that in this section `IsSimpleOrder` is the last type-class argument.
section DecidableEq

variable [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

/-- Every simple lattice is isomorphic to `Bool`, regardless of order. -/
@[simps]
/--
Definition of `equivBool` / `equivBool` 的定义

English:
definition equivBool
  signature: {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α]
  body: x = ⊤
  invFun x := x.casesOn ⊥ ⊤
  left_inv x := by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top]
  right_inv x := by cases x <;> simp [bot_ne_top]

中文:
定义 equiv布尔
  签名: {α} [DecidableEq α] [LE α] [有界序 α] [是单序 α]
  定义体: x = ⊤
  invFun x := x.casesOn ⊥ ⊤
  left_inv x := by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top]
  right_inv x := by cases x <;> simp [bot_ne_top]
-/
def equivBool {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : α ≃ Bool where
  toFun x := x = ⊤
  invFun x := x.casesOn ⊥ ⊤
  left_inv x := by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top]
  right_inv x := by cases x <;> simp [bot_ne_top]

/--
Definition of `orderIsoBool` / `orderIsoBool` 的定义

English:
definition orderIsoBool
  signature: : α ≃o Bool
  body: { equivBool with
    map_rel_iff' := @fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, Bool.false_lt_true]
        · simp }

中文:
定义 orderIso布尔
  签名: : α ≃o 布尔值
  定义体: { equivBool with
    map_rel_iff' := @fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, Bool.false_lt_true]
        · simp }

Depends on / 依赖: Bool.false_lt_true, bot_ne_top, bot_ne_top.symm, eq_bot_or_eq_top, equivBool, false_lt_true, map_rel_iff
-/
def orderIsoBool : α ≃o Bool :=
  { equivBool with
    map_rel_iff' := @fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, Bool.false_lt_true]
        · simp }

/-- A simple `BoundedOrder` is also a `BooleanAlgebra`. -/
@[instance_reducible]
/--
Definition of `booleanAlgebra` / `booleanAlgebra` 的定义

English:
definition booleanAlgebra
  signature: {α} [DecidableEq α] [Lattice α] [BoundedOrder α] [IsSimpleOrder α]
  body: { (inferInstance : BoundedOrder α), IsSimpleOrder.distribLattice with
    compl := fun x => if x = ⊥ then ⊤ else ⊥
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp
    inf_compl_le_bot := fun x => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
      · simp
    top_le_sup_compl := fun x => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }

中文:
定义 booleanAlgebra
  签名: {α} [DecidableEq α] [格 α] [有界序 α] [是单序 α]
  定义体: { (inferInstance : BoundedOrder α), IsSimpleOrder.distribLattice with
    compl := fun x => if x = ⊥ then ⊤ else ⊥
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp
    inf_compl_le_bot := fun x => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
      · simp
    top_le_sup_compl := fun x => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
-/
protected def booleanAlgebra {α} [DecidableEq α] [Lattice α] [BoundedOrder α] [IsSimpleOrder α] :
    BooleanAlgebra α :=
  { (inferInstance : BoundedOrder α), IsSimpleOrder.distribLattice with
    compl := fun x => if x = ⊥ then ⊤ else ⊥
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp
    inf_compl_le_bot := fun x => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
      · simp
    top_le_sup_compl := fun x => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }

end DecidableEq

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

open scoped Classical in
/-- A simple `BoundedOrder` is also complete. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def completeLattice
  body: { (inferInstance : Lattice α),
    (inferInstance : BoundedOrder α) with
    sSup := fun s => if ⊤ in s then ⊤ else ⊥
    sInf := fun s => if ⊥ in s then ⊥ else ⊤
    isLUB_sSup s := by
      refine ⟨fun x h => ?_, fun x h => ?_⟩
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · exact bot_le
        · rw [if_pos h]
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · rw [if_neg]
          intro con
          exact bot_ne_top (eq_top_iff.2 (h con))
        · exact le_top
    isGLB_sInf s := by
      refine ⟨fun x h => ?_, fun x h => ?_⟩
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · rw [if_pos h]
        · exact le_top
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · exact bot_le
        · rw [if_neg]
          intro con
          exact top_ne_bot (eq_bot_iff.2 (h con)) }

中文:
定义 noncomputable
  签名: def completeLattice
  定义体: { (inferInstance : Lattice α),
    (inferInstance : BoundedOrder α) with
    sSup := fun s => if ⊤ in s then ⊤ else ⊥
    sInf := fun s => if ⊥ in s then ⊥ else ⊤
    isLUB_sSup s := by
      refine ⟨fun x h => ?_, fun x h => ?_⟩
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · exact bot_le
        · rw [if_pos h]
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · rw [if_neg]
          intro con
          exact bot_ne_top (eq_top_iff.2 (h con))
        · exact le_top
    isGLB_sInf s := by
      refine ⟨fun x h => ?_, fun x h => ?_⟩
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · rw [if_pos h]
        · exact le_top
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · exact bot_le
        · rw [if_neg]
          intro con
          exact top_ne_bot (eq_bot_iff.2 (h con)) }
-/
protected noncomputable def completeLattice : CompleteLattice α :=
  { (inferInstance : Lattice α),
    (inferInstance : BoundedOrder α) with
    sSup := fun s => if ⊤ in s then ⊤ else ⊥
    sInf := fun s => if ⊥ in s then ⊥ else ⊤
    isLUB_sSup s := by
      refine ⟨fun x h => ?_, fun x h => ?_⟩
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · exact bot_le
        · rw [if_pos h]
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · rw [if_neg]
          intro con
          exact bot_ne_top (eq_top_iff.2 (h con))
        · exact le_top
    isGLB_sInf s := by
      refine ⟨fun x h => ?_, fun x h => ?_⟩
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · rw [if_pos h]
        · exact le_top
      · rcases eq_bot_or_eq_top x with (rfl | rfl)
        · exact bot_le
        · rw [if_neg]
          intro con
          exact top_ne_bot (eq_bot_iff.2 (h con)) }

open scoped Classical in
/-- A simple `BoundedOrder` is also a `CompleteBooleanAlgebra`. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def completeBooleanAlgebra
  body: { __ := IsSimpleOrder.completeLattice
    __ := IsSimpleOrder.booleanAlgebra }

中文:
定义 noncomputable
  签名: def complete布尔eanAlgebra
  定义体: { __ := IsSimpleOrder.completeLattice
    __ := IsSimpleOrder.booleanAlgebra }
-/
protected noncomputable def completeBooleanAlgebra : CompleteBooleanAlgebra α :=
  { __ := IsSimpleOrder.completeLattice
    __ := IsSimpleOrder.booleanAlgebra }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ComplementedLattice α
  body: letI := IsSimpleOrder.completeBooleanAlgebra (α := α); inferInstance

中文:
实例 :
  签名: 有补格 α
  定义体: letI := IsSimpleOrder.completeBooleanAlgebra (α := α); inferInstance

Depends on / 依赖: IsSimpleOrder, IsSimpleOrder.completeBooleanAlgebra, completeBooleanAlgebra
-/
instance : ComplementedLattice α :=
  letI := IsSimpleOrder.completeBooleanAlgebra (α := α); inferInstance

end IsSimpleOrder

namespace IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

instance (priority := 100) : IsAtomistic α where
  isLUB_atoms b := (eq_bot_or_eq_top b).elim (fun h => ⟨∅, by simp [h]⟩) (fun h => ⟨{⊤}, by simp [h]⟩)

instance (priority := 100) : IsCoatomistic α :=
  isAtomistic_dual_iff_isCoatomistic.1 (by infer_instance)

/--
lemma `bot_lt_iff_eq_top` / 引理 `bot_lt_iff_eq_top`

English:
lemma bot_lt_iff_eq_top
  given: {a : α}
  statement: ⊥ < a ↔ a = ⊤
  proof: ⟨eq_top_of_lt, fun h => h ▸ bot_lt_top⟩

中文:
引理 bot_lt_iff_eq_top
  条件: {a : α}
  结论: ⊥ < a ↔ a = ⊤
  证明: ⟨eq_top_of_lt, fun h => h ▸ bot_lt_top⟩
-/
@[simp] lemma bot_lt_iff_eq_top {a : α} : ⊥ < a ↔ a = ⊤ :=
  ⟨eq_top_of_lt, fun h => h ▸ bot_lt_top⟩

/--
lemma `lt_top_iff_eq_bot` / 引理 `lt_top_iff_eq_bot`

English:
lemma lt_top_iff_eq_bot
  given: {a : α}
  statement: a < ⊤ ↔ a = ⊥
  proof: ⟨eq_bot_of_lt, fun h => h ▸ bot_lt_top⟩

中文:
引理 lt_top_iff_eq_bot
  条件: {a : α}
  结论: a < ⊤ ↔ a = ⊥
  证明: ⟨eq_bot_of_lt, fun h => h ▸ bot_lt_top⟩
-/
@[simp] lemma lt_top_iff_eq_bot {a : α} : a < ⊤ ↔ a = ⊥ :=
  ⟨eq_bot_of_lt, fun h => h ▸ bot_lt_top⟩

end IsSimpleOrder

/--
theorem `isSimpleOrder_iff_isAtom_top` / 定理 `isSimpleOrder_iff_isAtom_top`

English:
theorem isSimpleOrder_iff_isAtom_top
  given: [PartialOrder α] [BoundedOrder α]
  proof: ⟨fun h => @isAtom_top _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊤, ⊥, h.1⟩
      eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩

中文:
定理 isSimpleOrder_iff_isAtom_top
  条件: [偏序 α] [有界序 α]
  证明: ⟨fun h => @isAtom_top _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊤, ⊥, h.1⟩
      eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩

Depends on / 依赖: eq_bot_or_eq_top, eq_or_lt_of_le, exists_pair_ne, imp_right, isAtom_top, le_top
-/
theorem isSimpleOrder_iff_isAtom_top [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsAtom (⊤ : α) :=
  ⟨fun h => @isAtom_top _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊤, ⊥, h.1⟩
      eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩

/--
theorem `isSimpleOrder_iff_isCoatom_bot` / 定理 `isSimpleOrder_iff_isCoatom_bot`

English:
theorem isSimpleOrder_iff_isCoatom_bot
  given: [PartialOrder α] [BoundedOrder α]
  proof: isSimpleOrder_iff_isSimpleOrder_orderDual.trans isSimpleOrder_iff_isAtom_top

中文:
定理 isSimpleOrder_iff_isCoatom_bot
  条件: [偏序 α] [有界序 α]
  证明: isSimpleOrder_iff_isSimpleOrder_orderDual.trans isSimpleOrder_iff_isAtom_top

Depends on / 依赖: isSimpleOrder_iff_isAtom_top, isSimpleOrder_iff_isSimpleOrder_orderDual, isSimpleOrder_iff_isSimpleOrder_orderDual.trans
-/
theorem isSimpleOrder_iff_isCoatom_bot [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsCoatom (⊥ : α) :=
  isSimpleOrder_iff_isSimpleOrder_orderDual.trans isSimpleOrder_iff_isAtom_top

namespace Set

/--
theorem `isSimpleOrder_Iic_iff_isAtom` / 定理 `isSimpleOrder_Iic_iff_isAtom`

English:
theorem isSimpleOrder_Iic_iff_isAtom
  given: [PartialOrder α] [OrderBot α] {a : α}
  proof: isSimpleOrder_iff_isAtom_top.trans
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

中文:
定理 isSimpleOrder_Iic_iff_isAtom
  条件: [偏序 α] [有底序 α] {a : α}
  证明: isSimpleOrder_iff_isAtom_top.trans
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, Subtype.mk_lt_mk, and_congr, isSimpleOrder_iff_isAtom_top, isSimpleOrder_iff_isAtom_top.trans, le_of_lt, mk_eq_mk, mk_lt_mk, not_congr
-/
theorem isSimpleOrder_Iic_iff_isAtom [PartialOrder α] [OrderBot α] {a : α} :
    IsSimpleOrder (Iic a) ↔ IsAtom a :=
isSimpleOrder_iff_isAtom_top.trans
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

/--
theorem `isSimpleOrder_Ici_iff_isCoatom` / 定理 `isSimpleOrder_Ici_iff_isCoatom`

English:
theorem isSimpleOrder_Ici_iff_isCoatom
  given: [PartialOrder α] [OrderTop α] {a : α}
  proof: isSimpleOrder_iff_isCoatom_bot.trans
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

中文:
定理 isSimpleOrder_Ici_iff_isCoatom
  条件: [偏序 α] [有顶序 α] {a : α}
  证明: isSimpleOrder_iff_isCoatom_bot.trans
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, Subtype.mk_lt_mk, and_congr, isSimpleOrder_iff_isCoatom_bot, isSimpleOrder_iff_isCoatom_bot.trans, le_of_lt, mk_eq_mk, mk_lt_mk, not_congr
-/
theorem isSimpleOrder_Ici_iff_isCoatom [PartialOrder α] [OrderTop α] {a : α} :
    IsSimpleOrder (Ici a) ↔ IsCoatom a :=
isSimpleOrder_iff_isCoatom_bot.trans
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

end Set

namespace OrderEmbedding

variable [PartialOrder α] [PartialOrder β]

/--
theorem `isAtom_of_map_bot_of_image` / 定理 `isAtom_of_map_bot_of_image`

English:
theorem isAtom_of_map_bot_of_image
  statement: [OrderBot α] [OrderBot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β}
  proof: by
  simp only [← bot_covBy_iff] at hb ⊢
  exact CovBy.of_image f (hbot.symm ▸ hb)

中文:
定理 isAtom_of_map_bot_of_image
  结论: [有底序 α] [有底序 β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β}
  证明: by
  simp only [← bot_covBy_iff] at hb ⊢
  exact CovBy.of_image f (hbot.symm ▸ hb)

Depends on / 依赖: CovBy.of_image, bot_covBy_iff, hbot.symm, of_image
-/
theorem isAtom_of_map_bot_of_image [OrderBot α] [OrderBot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β}
    (hb : IsAtom (f b)) : IsAtom b := by
  simp only [← bot_covBy_iff] at hb ⊢
  exact CovBy.of_image f (hbot.symm ▸ hb)

/--
theorem `isCoatom_of_map_top_of_image` / 定理 `isCoatom_of_map_top_of_image`

English:
theorem isCoatom_of_map_top_of_image
  statement: [OrderTop α] [OrderTop β] (f : β ↪o α) (htop : f ⊤ = ⊤)
  proof: f.dual.isAtom_of_map_bot_of_image htop hb

中文:
定理 isCoatom_of_map_top_of_image
  结论: [有顶序 α] [有顶序 β] (f : β ↪o α) (htop : f ⊤ = ⊤)
  证明: f.dual.isAtom_of_map_bot_of_image htop hb

Depends on / 依赖: f.dual.isAtom_of_map_bot_of_image, isAtom_of_map_bot_of_image
-/
theorem isCoatom_of_map_top_of_image [OrderTop α] [OrderTop β] (f : β ↪o α) (htop : f ⊤ = ⊤)
    {b : β} (hb : IsCoatom (f b)) : IsCoatom b :=
  f.dual.isAtom_of_map_bot_of_image htop hb

end OrderEmbedding

namespace GaloisInsertion

variable [PartialOrder α] [PartialOrder β]

/--
theorem `isAtom_of_u_bot` / 定理 `isAtom_of_u_bot`

English:
theorem isAtom_of_u_bot
  statement: [OrderBot α] [OrderBot β] {l : α -> β} {u : β -> α}
  proof: OrderEmbedding.isAtom_of_map_bot_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ hbot hb

中文:
定理 isAtom_of_u_bot
  结论: [有底序 α] [有底序 β] {l : α -> β} {u : β -> α}
  证明: OrderEmbedding.isAtom_of_map_bot_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ hbot hb

Depends on / 依赖: GaloisInsertion, GaloisInsertion.u_le_u_iff, OrderEmbedding, OrderEmbedding.isAtom_of_map_bot_of_image, gi.u_injective, isAtom_of_map_bot_of_image, u_injective, u_le_u_iff
-/
theorem isAtom_of_u_bot [OrderBot α] [OrderBot β] {l : α -> β} {u : β -> α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) {b : β} (hb : IsAtom (u b)) : IsAtom b :=
  OrderEmbedding.isAtom_of_map_bot_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ hbot hb

/--
theorem `isAtom_iff` / 定理 `isAtom_iff`

English:
theorem isAtom_iff
  statement: [OrderBot α] [IsAtomic α] [OrderBot β] {l : α -> β} {u : β -> α}
  proof: by
  refine ⟨fun hla => ?_, fun ha => gi.isAtom_of_u_bot hbot ((h_atom a ha).symm ▸ ha)⟩
  obtain ⟨a', ha', hab'⟩ :=
    (eq_bot_or_exists_atom_le (u (l a))).resolve_left (hbot ▸ fun h => hla.1 (gi.u_injective h))
  have :=
    (hla.le_iff.mp <| (gi.l_u_eq (l a) ▸ gi.gc.monotone_l hab' : l a' <= l a)).resolve_left fun h =>
      ha'.1 (hbot ▸ h_atom a' ha' ▸ congr_arg u h)
  have haa' : a = a' :=
    (ha'.le_iff.mp <|
          (gi.gc.le_u_l a).trans_eq (h_atom a' ha' ▸ congr_arg u this.symm)).resolve_left
      (mt (congr_arg l) (gi.gc.l_bot.symm ▸ hla.1))
  exact haa'.symm ▸ ha'

中文:
定理 isAtom_iff
  结论: [有底序 α] [是原子的 α] [有底序 β] {l : α -> β} {u : β -> α}
  证明: by
  refine ⟨fun hla => ?_, fun ha => gi.isAtom_of_u_bot hbot ((h_atom a ha).symm ▸ ha)⟩
  obtain ⟨a', ha', hab'⟩ :=
    (eq_bot_or_exists_atom_le (u (l a))).resolve_left (hbot ▸ fun h => hla.1 (gi.u_injective h))
  have :=
    (hla.le_iff.mp <| (gi.l_u_eq (l a) ▸ gi.gc.monotone_l hab' : l a' <= l a)).resolve_left fun h =>
      ha'.1 (hbot ▸ h_atom a' ha' ▸ congr_arg u h)
  have haa' : a = a' :=
    (ha'.le_iff.mp <|
          (gi.gc.le_u_l a).trans_eq (h_atom a' ha' ▸ congr_arg u this.symm)).resolve_left
      (mt (congr_arg l) (gi.gc.l_bot.symm ▸ hla.1))
  exact haa'.symm ▸ ha'

Depends on / 依赖: congr_arg, eq_bot_or_exists_atom_le, gi.gc, gi.gc.le_u_l, gi.gc.monotone_l, gi.isAtom_of_u_bot, gi.l_u_eq, gi.u_injective, h_atom, hla.le_iff.mp, isAtom_of_u_bot, l_u_eq, le_iff, le_iff.mp, le_u_l, monotone_l, resolve_left, this.symm, trans_eq, u_injective
-/
theorem isAtom_iff [OrderBot α] [IsAtomic α] [OrderBot β] {l : α -> β} {u : β -> α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : forall a, IsAtom a -> u (l a) = a) (a : α) :
    IsAtom (l a) ↔ IsAtom a := by
  refine ⟨fun hla => ?_, fun ha => gi.isAtom_of_u_bot hbot ((h_atom a ha).symm ▸ ha)⟩
  obtain ⟨a', ha', hab'⟩ :=
    (eq_bot_or_exists_atom_le (u (l a))).resolve_left (hbot ▸ fun h => hla.1 (gi.u_injective h))
  have :=
    (hla.le_iff.mp <| (gi.l_u_eq (l a) ▸ gi.gc.monotone_l hab' : l a' <= l a)).resolve_left fun h =>
      ha'.1 (hbot ▸ h_atom a' ha' ▸ congr_arg u h)
  have haa' : a = a' :=
    (ha'.le_iff.mp <|
          (gi.gc.le_u_l a).trans_eq (h_atom a' ha' ▸ congr_arg u this.symm)).resolve_left
      (mt (congr_arg l) (gi.gc.l_bot.symm ▸ hla.1))
  exact haa'.symm ▸ ha'

/--
theorem `isAtom_iff'` / 定理 `isAtom_iff'`

English:
theorem isAtom_iff'
  statement: [OrderBot α] [IsAtomic α] [OrderBot β] {l : α -> β} {u : β -> α}
  proof: by rw [← gi.isAtom_iff hbot h_atom, gi.l_u_eq]

中文:
定理 isAtom_iff'
  结论: [有底序 α] [是原子的 α] [有底序 β] {l : α -> β} {u : β -> α}
  证明: by rw [← gi.isAtom_iff hbot h_atom, gi.l_u_eq]

Depends on / 依赖: gi.isAtom_iff, gi.l_u_eq, h_atom, isAtom_iff, l_u_eq
-/
theorem isAtom_iff' [OrderBot α] [IsAtomic α] [OrderBot β] {l : α -> β} {u : β -> α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : forall a, IsAtom a -> u (l a) = a) (b : β) :
    IsAtom (u b) ↔ IsAtom b := by rw [← gi.isAtom_iff hbot h_atom, gi.l_u_eq]

/--
theorem `isCoatom_of_image` / 定理 `isCoatom_of_image`

English:
theorem isCoatom_of_image
  statement: [OrderTop α] [OrderTop β] {l : α -> β} {u : β -> α}
  proof: OrderEmbedding.isCoatom_of_map_top_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ gi.gc.u_top hb

中文:
定理 isCoatom_of_image
  结论: [有顶序 α] [有顶序 β] {l : α -> β} {u : β -> α}
  证明: OrderEmbedding.isCoatom_of_map_top_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ gi.gc.u_top hb

Depends on / 依赖: GaloisInsertion, GaloisInsertion.u_le_u_iff, OrderEmbedding, OrderEmbedding.isCoatom_of_map_top_of_image, gi.gc.u_top, gi.u_injective, isCoatom_of_map_top_of_image, u_injective, u_le_u_iff, u_top
-/
theorem isCoatom_of_image [OrderTop α] [OrderTop β] {l : α -> β} {u : β -> α}
    (gi : GaloisInsertion l u) {b : β} (hb : IsCoatom (u b)) : IsCoatom b :=
  OrderEmbedding.isCoatom_of_map_top_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ gi.gc.u_top hb

/--
theorem `isCoatom_iff` / 定理 `isCoatom_iff`

English:
theorem isCoatom_iff
  statement: [OrderTop α] [IsCoatomic α] [OrderTop β] {l : α -> β} {u : β -> α}
  proof: by
  refine ⟨fun hb => gi.isCoatom_of_image hb, fun hb => ?_⟩
  obtain ⟨a, ha, hab⟩ :=
    (eq_top_or_exists_le_coatom (u b)).resolve_left fun h =>
hb.1 (gi.gc.u_top ▸ gi.l_u_eq ⊤ : l ⊤ = ⊤) ▸ gi.l_u_eq b ▸ congr_arg l h
  have : l a = b :=
    (hb.le_iff.mp (gi.l_u_eq b ▸ gi.gc.monotone_l hab : b <= l a)).resolve_left fun hla =>
      ha.1 (gi.gc.u_top ▸ h_coatom a ha ▸ congr_arg u hla)
  exact this ▸ (h_coatom a ha).symm ▸ ha

中文:
定理 isCoatom_iff
  结论: [有顶序 α] [是余原子的 α] [有顶序 β] {l : α -> β} {u : β -> α}
  证明: by
  refine ⟨fun hb => gi.isCoatom_of_image hb, fun hb => ?_⟩
  obtain ⟨a, ha, hab⟩ :=
    (eq_top_or_exists_le_coatom (u b)).resolve_left fun h =>
hb.1 (gi.gc.u_top ▸ gi.l_u_eq ⊤ : l ⊤ = ⊤) ▸ gi.l_u_eq b ▸ congr_arg l h
  have : l a = b :=
    (hb.le_iff.mp (gi.l_u_eq b ▸ gi.gc.monotone_l hab : b <= l a)).resolve_left fun hla =>
      ha.1 (gi.gc.u_top ▸ h_coatom a ha ▸ congr_arg u hla)
  exact this ▸ (h_coatom a ha).symm ▸ ha

Depends on / 依赖: congr_arg, eq_top_or_exists_le_coatom, gi.gc.monotone_l, gi.gc.u_top, gi.isCoatom_of_image, gi.l_u_eq, h_coatom, hb.le_iff.mp, isCoatom_of_image, l_u_eq, le_iff, monotone_l, resolve_left, u_top
-/
theorem isCoatom_iff [OrderTop α] [IsCoatomic α] [OrderTop β] {l : α -> β} {u : β -> α}
    (gi : GaloisInsertion l u) (h_coatom : forall a : α, IsCoatom a -> u (l a) = a) (b : β) :
    IsCoatom (u b) ↔ IsCoatom b := by
  refine ⟨fun hb => gi.isCoatom_of_image hb, fun hb => ?_⟩
  obtain ⟨a, ha, hab⟩ :=
    (eq_top_or_exists_le_coatom (u b)).resolve_left fun h =>
hb.1 (gi.gc.u_top ▸ gi.l_u_eq ⊤ : l ⊤ = ⊤) ▸ gi.l_u_eq b ▸ congr_arg l h
  have : l a = b :=
    (hb.le_iff.mp (gi.l_u_eq b ▸ gi.gc.monotone_l hab : b <= l a)).resolve_left fun hla =>
      ha.1 (gi.gc.u_top ▸ h_coatom a ha ▸ congr_arg u hla)
  exact this ▸ (h_coatom a ha).symm ▸ ha

end GaloisInsertion

namespace GaloisCoinsertion

variable [PartialOrder α] [PartialOrder β]

/--
theorem `isCoatom_of_l_top` / 定理 `isCoatom_of_l_top`

English:
theorem isCoatom_of_l_top
  statement: [OrderTop α] [OrderTop β] {l : α -> β} {u : β -> α}
  proof: gi.dual.isAtom_of_u_bot hbot hb.dual

中文:
定理 isCoatom_of_l_top
  结论: [有顶序 α] [有顶序 β] {l : α -> β} {u : β -> α}
  证明: gi.dual.isAtom_of_u_bot hbot hb.dual

Depends on / 依赖: gi.dual.isAtom_of_u_bot, hb.dual, isAtom_of_u_bot
-/
theorem isCoatom_of_l_top [OrderTop α] [OrderTop β] {l : α -> β} {u : β -> α}
    (gi : GaloisCoinsertion l u) (hbot : l ⊤ = ⊤) {a : α} (hb : IsCoatom (l a)) : IsCoatom a :=
  gi.dual.isAtom_of_u_bot hbot hb.dual

/--
theorem `isCoatom_iff` / 定理 `isCoatom_iff`

English:
theorem isCoatom_iff
  statement: [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α -> β} {u : β -> α}
  proof: gi.dual.isAtom_iff htop h_coatom b

中文:
定理 isCoatom_iff
  结论: [有顶序 α] [有顶序 β] [是余原子的 β] {l : α -> β} {u : β -> α}
  证明: gi.dual.isAtom_iff htop h_coatom b

Depends on / 依赖: gi.dual.isAtom_iff, h_coatom, isAtom_iff
-/
theorem isCoatom_iff [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α -> β} {u : β -> α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : forall b, IsCoatom b -> l (u b) = b)
    (b : β) : IsCoatom (u b) ↔ IsCoatom b :=
  gi.dual.isAtom_iff htop h_coatom b

/--
theorem `isCoatom_iff'` / 定理 `isCoatom_iff'`

English:
theorem isCoatom_iff'
  statement: [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α -> β} {u : β -> α}
  proof: gi.dual.isAtom_iff' htop h_coatom a

中文:
定理 isCoatom_iff'
  结论: [有顶序 α] [有顶序 β] [是余原子的 β] {l : α -> β} {u : β -> α}
  证明: gi.dual.isAtom_iff' htop h_coatom a

Depends on / 依赖: gi.dual.isAtom_iff, h_coatom, isAtom_iff
-/
theorem isCoatom_iff' [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α -> β} {u : β -> α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : forall b, IsCoatom b -> l (u b) = b)
    (a : α) : IsCoatom (l a) ↔ IsCoatom a :=
  gi.dual.isAtom_iff' htop h_coatom a

/--
theorem `isAtom_of_image` / 定理 `isAtom_of_image`

English:
theorem isAtom_of_image
  statement: [OrderBot α] [OrderBot β] {l : α -> β} {u : β -> α}
  proof: gi.dual.isCoatom_of_image hb.dual

中文:
定理 isAtom_of_image
  结论: [有底序 α] [有底序 β] {l : α -> β} {u : β -> α}
  证明: gi.dual.isCoatom_of_image hb.dual

Depends on / 依赖: gi.dual.isCoatom_of_image, hb.dual, isCoatom_of_image
-/
theorem isAtom_of_image [OrderBot α] [OrderBot β] {l : α -> β} {u : β -> α}
    (gi : GaloisCoinsertion l u) {a : α} (hb : IsAtom (l a)) : IsAtom a :=
  gi.dual.isCoatom_of_image hb.dual

/--
theorem `isAtom_iff` / 定理 `isAtom_iff`

English:
theorem isAtom_iff
  statement: [OrderBot α] [OrderBot β] [IsAtomic β] {l : α -> β} {u : β -> α}
  proof: gi.dual.isCoatom_iff h_atom a

中文:
定理 isAtom_iff
  结论: [有底序 α] [有底序 β] [是原子的 β] {l : α -> β} {u : β -> α}
  证明: gi.dual.isCoatom_iff h_atom a

Depends on / 依赖: gi.dual.isCoatom_iff, h_atom, isCoatom_iff
-/
theorem isAtom_iff [OrderBot α] [OrderBot β] [IsAtomic β] {l : α -> β} {u : β -> α}
    (gi : GaloisCoinsertion l u) (h_atom : forall b, IsAtom b -> l (u b) = b) (a : α) :
    IsAtom (l a) ↔ IsAtom a :=
  gi.dual.isCoatom_iff h_atom a

end GaloisCoinsertion

namespace OrderIso

variable [PartialOrder α] [PartialOrder β]

@[simp]
/--
theorem `isAtom_iff` / 定理 `isAtom_iff`

English:
theorem isAtom_iff
  given: [OrderBot α] [OrderBot β] (f : α ≃o β) (a : α)
  statement: IsAtom (f a) ↔ IsAtom a
  proof: ⟨f.toGaloisCoinsertion.isAtom_of_image, fun ha =>
f.toGaloisInsertion.isAtom_of_u_bot (map_bot f.symm) (f.symm_apply_apply a).symm ▸ ha⟩

@[simp]

中文:
定理 isAtom_iff
  条件: [有底序 α] [有底序 β] (f : α ≃o β) (a : α)
  结论: IsAtom (f a) ↔ IsAtom a
  证明: ⟨f.toGaloisCoinsertion.isAtom_of_image, fun ha =>
f.toGaloisInsertion.isAtom_of_u_bot (map_bot f.symm) (f.symm_apply_apply a).symm ▸ ha⟩

@[simp]

Depends on / 依赖: f.symm, f.symm_apply_apply, f.toGaloisCoinsertion.isAtom_of_image, f.toGaloisInsertion.isAtom_of_u_bot, isAtom_of_image, isAtom_of_u_bot, map_bot, symm_apply_apply, toGaloisCoinsertion, toGaloisInsertion
-/
theorem isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (a : α) : IsAtom (f a) ↔ IsAtom a :=
  ⟨f.toGaloisCoinsertion.isAtom_of_image, fun ha =>
f.toGaloisInsertion.isAtom_of_u_bot (map_bot f.symm) (f.symm_apply_apply a).symm ▸ ha⟩

@[simp]
/--
theorem `isCoatom_iff` / 定理 `isCoatom_iff`

English:
theorem isCoatom_iff
  given: [OrderTop α] [OrderTop β] (f : α ≃o β) (a : α)
  proof: f.dual.isAtom_iff a

中文:
定理 isCoatom_iff
  条件: [有顶序 α] [有顶序 β] (f : α ≃o β) (a : α)
  证明: f.dual.isAtom_iff a

Depends on / 依赖: f.dual.isAtom_iff, isAtom_iff
-/
theorem isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o β) (a : α) :
    IsCoatom (f a) ↔ IsCoatom a :=
  f.dual.isAtom_iff a

/--
theorem `isSimpleOrder_iff` / 定理 `isSimpleOrder_iff`

English:
theorem isSimpleOrder_iff
  given: [BoundedOrder α] [BoundedOrder β] (f : α ≃o β)
  proof: by
  rw [isSimpleOrder_iff_isAtom_top]; rw [isSimpleOrder_iff_isAtom_top]; rw [← f.isAtom_iff ⊤]; rw [f.map_top]

中文:
定理 isSimpleOrder_iff
  条件: [有界序 α] [有界序 β] (f : α ≃o β)
  证明: by
  rw [isSimpleOrder_iff_isAtom_top]; rw [isSimpleOrder_iff_isAtom_top]; rw [← f.isAtom_iff ⊤]; rw [f.map_top]

Depends on / 依赖: f.isAtom_iff, f.map_top, isAtom_iff, isSimpleOrder_iff_isAtom_top, map_top
-/
theorem isSimpleOrder_iff [BoundedOrder α] [BoundedOrder β] (f : α ≃o β) :
    IsSimpleOrder α ↔ IsSimpleOrder β := by
  rw [isSimpleOrder_iff_isAtom_top]; rw [isSimpleOrder_iff_isAtom_top]; rw [← f.isAtom_iff ⊤]; rw [f.map_top]

/--
theorem `isSimpleOrder` / 定理 `isSimpleOrder`

English:
theorem isSimpleOrder
  given: [BoundedOrder α] [BoundedOrder β] [h : IsSimpleOrder β] (f : α ≃o β)
  proof: f.isSimpleOrder_iff.mpr h

中文:
定理 isSimpleOrder
  条件: [有界序 α] [有界序 β] [h : 是单序 β] (f : α ≃o β)
  证明: f.isSimpleOrder_iff.mpr h

Depends on / 依赖: f.isSimpleOrder_iff.mpr, isSimpleOrder_iff
-/
theorem isSimpleOrder [BoundedOrder α] [BoundedOrder β] [h : IsSimpleOrder β] (f : α ≃o β) :
    IsSimpleOrder α :=
  f.isSimpleOrder_iff.mpr h

/--
theorem `isAtomic_iff` / 定理 `isAtomic_iff`

English:
theorem isAtomic_iff
  given: [OrderBot α] [OrderBot β] (f : α ≃o β)
  proof: by
  simp only [isAtomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
    f.le_iff_le, f.isAtom_iff]

中文:
定理 isAtomic_iff
  条件: [有底序 α] [有底序 β] (f : α ≃o β)
  证明: by
  simp only [isAtomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
    f.le_iff_le, f.isAtom_iff]
-/
protected theorem isAtomic_iff [OrderBot α] [OrderBot β] (f : α ≃o β) :
    IsAtomic α ↔ IsAtomic β := by
  simp only [isAtomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
    f.le_iff_le, f.isAtom_iff]

/--
theorem `isCoatomic_iff` / 定理 `isCoatomic_iff`

English:
theorem isCoatomic_iff
  given: [OrderTop α] [OrderTop β] (f : α ≃o β)
  proof: by
  simp only [← isAtomic_dual_iff_isCoatomic, f.dual.isAtomic_iff]

中文:
定理 isCoatomic_iff
  条件: [有顶序 α] [有顶序 β] (f : α ≃o β)
  证明: by
  simp only [← isAtomic_dual_iff_isCoatomic, f.dual.isAtomic_iff]
-/
protected theorem isCoatomic_iff [OrderTop α] [OrderTop β] (f : α ≃o β) :
    IsCoatomic α ↔ IsCoatomic β := by
  simp only [← isAtomic_dual_iff_isCoatomic, f.dual.isAtomic_iff]

end OrderIso
section Lattice

variable [Lattice α]

/--
theorem `Lattice.isStronglyAtomic` / 定理 `Lattice.isStronglyAtomic`

English:
theorem Lattice.isStronglyAtomic
  given: [OrderBot α] [IsUpperModularLattice α] [IsAtomistic α]
  proof: by
    obtain ⟨s, hsb, h⟩ := isLUB_atoms b
refine by_contra fun hcon => hab.not_ge (isLUB_le_iff hsb).2 fun x hx => ?_
    simp_rw [not_exists, and_comm (b := _ <= _), not_and] at hcon
    specialize hcon (x ⊔ a) (sup_le (hsb.1 hx) hab.le)
    obtain (hbot | h_inf) := (h x hx).bot_covBy.eq_or_eq (c := x ⊓ a) (by simp) (by simp)
· exact False.elim hcon
        (hbot ▸ IsUpperModularLattice.covBy_sup_of_inf_covBy) (h x hx).bot_covBy
    rwa [inf_eq_left] at h_inf

中文:
定理 格.isStronglyAtomic
  条件: [有底序 α] [是UpperModular格 α] [是Atomistic α]
  证明: by
    obtain ⟨s, hsb, h⟩ := isLUB_atoms b
refine by_contra fun hcon => hab.not_ge (isLUB_le_iff hsb).2 fun x hx => ?_
    simp_rw [not_exists, and_comm (b := _ <= _), not_and] at hcon
    specialize hcon (x ⊔ a) (sup_le (hsb.1 hx) hab.le)
    obtain (hbot | h_inf) := (h x hx).bot_covBy.eq_or_eq (c := x ⊓ a) (by simp) (by simp)
· exact False.elim hcon
        (hbot ▸ IsUpperModularLattice.covBy_sup_of_inf_covBy) (h x hx).bot_covBy
    rwa [inf_eq_left] at h_inf

Depends on / 依赖: False.elim, IsUpperModularLattice, IsUpperModularLattice.covBy_sup_of_inf_covBy, and_comm, bot_covBy, bot_covBy.eq_or_eq, covBy_sup_of_inf_covBy, eq_or_eq, h_inf, hab.le, hab.not_ge, inf_eq_left, isLUB_atoms, isLUB_le_iff, not_and, not_exists, not_ge, simp_rw, specialize, sup_le
-/
theorem Lattice.isStronglyAtomic [OrderBot α] [IsUpperModularLattice α] [IsAtomistic α] :
    IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨s, hsb, h⟩ := isLUB_atoms b
refine by_contra fun hcon => hab.not_ge (isLUB_le_iff hsb).2 fun x hx => ?_
    simp_rw [not_exists, and_comm (b := _ <= _), not_and] at hcon
    specialize hcon (x ⊔ a) (sup_le (hsb.1 hx) hab.le)
    obtain (hbot | h_inf) := (h x hx).bot_covBy.eq_or_eq (c := x ⊓ a) (by simp) (by simp)
· exact False.elim hcon
        (hbot ▸ IsUpperModularLattice.covBy_sup_of_inf_covBy) (h x hx).bot_covBy
    rwa [inf_eq_left] at h_inf

/--
theorem `Lattice.isStronglyCoatomic` / 定理 `Lattice.isStronglyCoatomic`

English:
theorem Lattice.isStronglyCoatomic
  statement: [OrderTop α] [IsLowerModularLattice α]
  proof: by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]
  exact Lattice.isStronglyAtomic

中文:
定理 格.isStronglyCoatomic
  结论: [有顶序 α] [是LowerModular格 α]
  证明: by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]
  exact Lattice.isStronglyAtomic

Depends on / 依赖: Lattice, Lattice.isStronglyAtomic, isStronglyAtomic, isStronglyAtomic_dual_iff_is_stronglyCoatomic
-/
theorem Lattice.isStronglyCoatomic [OrderTop α] [IsLowerModularLattice α]
    [IsCoatomistic α] : IsStronglyCoatomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]
  exact Lattice.isStronglyAtomic

end Lattice

section IsModularLattice

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

namespace IsCompl

variable {a b : α} (hc : IsCompl a b)
include hc

/--
theorem `isAtom_iff_isCoatom` / 定理 `isAtom_iff_isCoatom`

English:
theorem isAtom_iff_isCoatom
  statement: IsAtom a ↔ IsCoatom b
  proof: Set.isSimpleOrder_Iic_iff_isAtom.symm.trans
    hc.IicOrderIsoIci.isSimpleOrder_iff.trans Set.isSimpleOrder_Ici_iff_isCoatom

中文:
定理 isAtom_iff_isCoatom
  结论: IsAtom a ↔ IsCoatom b
  证明: Set.isSimpleOrder_Iic_iff_isAtom.symm.trans
    hc.IicOrderIsoIci.isSimpleOrder_iff.trans Set.isSimpleOrder_Ici_iff_isCoatom

Depends on / 依赖: IicOrderIsoIci, Set.isSimpleOrder_Ici_iff_isCoatom, Set.isSimpleOrder_Iic_iff_isAtom.symm.trans, hc.IicOrderIsoIci.isSimpleOrder_iff.trans, isSimpleOrder_Ici_iff_isCoatom, isSimpleOrder_Iic_iff_isAtom, isSimpleOrder_iff
-/
theorem isAtom_iff_isCoatom : IsAtom a ↔ IsCoatom b :=
Set.isSimpleOrder_Iic_iff_isAtom.symm.trans
    hc.IicOrderIsoIci.isSimpleOrder_iff.trans Set.isSimpleOrder_Ici_iff_isCoatom

/--
theorem `isCoatom_iff_isAtom` / 定理 `isCoatom_iff_isAtom`

English:
theorem isCoatom_iff_isAtom
  statement: IsCoatom a ↔ IsAtom b
  proof: hc.symm.isAtom_iff_isCoatom.symm

中文:
定理 isCoatom_iff_isAtom
  结论: IsCoatom a ↔ IsAtom b
  证明: hc.symm.isAtom_iff_isCoatom.symm

Depends on / 依赖: hc.symm.isAtom_iff_isCoatom.symm, isAtom_iff_isCoatom
-/
theorem isCoatom_iff_isAtom : IsCoatom a ↔ IsAtom b :=
  hc.symm.isAtom_iff_isCoatom.symm

end IsCompl

variable [ComplementedLattice α]

/--
theorem `isCoatomic_of_isAtomic_of_complementedLattice_of_isModular` / 定理 `isCoatomic_of_isAtomic_of_complementedLattice_of_isModular`

English:
theorem isCoatomic_of_isAtomic_of_complementedLattice_of_isModular
  given: [IsAtomic α]
  proof: ⟨fun x => by
    rcases exists_isCompl x with ⟨y, xy⟩
    apply (eq_bot_or_exists_atom_le y).imp _ _
    · rintro rfl
      exact eq_top_of_isCompl_bot xy
    · rintro ⟨a, ha, ay⟩
      rcases exists_isCompl (xy.symm.IicOrderIsoIci ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩
      refine ⟨↑(⟨b, xb⟩ : Set.Ici x), IsCoatom.of_isCoatom_coe_Ici ?_, xb⟩
      rw [← hb.isAtom_iff_isCoatom]; rw [OrderIso.isAtom_iff]
      apply ha.Iic⟩

中文:
定理 isCoatomic_of_isAtomic_of_complementedLattice_of_isModular
  条件: [是原子的 α]
  证明: ⟨fun x => by
    rcases exists_isCompl x with ⟨y, xy⟩
    apply (eq_bot_or_exists_atom_le y).imp _ _
    · rintro rfl
      exact eq_top_of_isCompl_bot xy
    · rintro ⟨a, ha, ay⟩
      rcases exists_isCompl (xy.symm.IicOrderIsoIci ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩
      refine ⟨↑(⟨b, xb⟩ : Set.Ici x), IsCoatom.of_isCoatom_coe_Ici ?_, xb⟩
      rw [← hb.isAtom_iff_isCoatom]; rw [OrderIso.isAtom_iff]
      apply ha.Iic⟩

Depends on / 依赖: IicOrderIsoIci, IsCoatom, IsCoatom.of_isCoatom_coe_Ici, OrderIso, OrderIso.isAtom_iff, Set.Ici, eq_bot_or_exists_atom_le, eq_top_of_isCompl_bot, exists_isCompl, ha.Iic, hb.isAtom_iff_isCoatom, isAtom_iff, isAtom_iff_isCoatom, of_isCoatom_coe_Ici, xy.symm.IicOrderIsoIci
-/
theorem isCoatomic_of_isAtomic_of_complementedLattice_of_isModular [IsAtomic α] :
    IsCoatomic α :=
  ⟨fun x => by
    rcases exists_isCompl x with ⟨y, xy⟩
    apply (eq_bot_or_exists_atom_le y).imp _ _
    · rintro rfl
      exact eq_top_of_isCompl_bot xy
    · rintro ⟨a, ha, ay⟩
      rcases exists_isCompl (xy.symm.IicOrderIsoIci ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩
      refine ⟨↑(⟨b, xb⟩ : Set.Ici x), IsCoatom.of_isCoatom_coe_Ici ?_, xb⟩
      rw [← hb.isAtom_iff_isCoatom]; rw [OrderIso.isAtom_iff]
      apply ha.Iic⟩

/--
theorem `isAtomic_of_isCoatomic_of_complementedLattice_of_isModular` / 定理 `isAtomic_of_isCoatomic_of_complementedLattice_of_isModular`

English:
theorem isAtomic_of_isCoatomic_of_complementedLattice_of_isModular
  given: [IsCoatomic α]
  proof: isCoatomic_dual_iff_isAtomic.1 isCoatomic_of_isAtomic_of_complementedLattice_of_isModular

中文:
定理 isAtomic_of_isCoatomic_of_complementedLattice_of_isModular
  条件: [是余原子的 α]
  证明: isCoatomic_dual_iff_isAtomic.1 isCoatomic_of_isAtomic_of_complementedLattice_of_isModular

Depends on / 依赖: isCoatomic_dual_iff_isAtomic, isCoatomic_of_isAtomic_of_complementedLattice_of_isModular
-/
theorem isAtomic_of_isCoatomic_of_complementedLattice_of_isModular [IsCoatomic α] :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.1 isCoatomic_of_isAtomic_of_complementedLattice_of_isModular

/--
theorem `isAtomic_iff_isCoatomic` / 定理 `isAtomic_iff_isCoatomic`

English:
theorem isAtomic_iff_isCoatomic
  statement: IsAtomic α ↔ IsCoatomic α
  proof: ⟨fun _ => isCoatomic_of_isAtomic_of_complementedLattice_of_isModular,
   fun _ => isAtomic_of_isCoatomic_of_complementedLattice_of_isModular⟩

中文:
定理 isAtomic_iff_isCoatomic
  结论: 是原子的 α ↔ 是余原子的 α
  证明: ⟨fun _ => isCoatomic_of_isAtomic_of_complementedLattice_of_isModular,
   fun _ => isAtomic_of_isCoatomic_of_complementedLattice_of_isModular⟩

Depends on / 依赖: isAtomic_of_isCoatomic_of_complementedLattice_of_isModular, isCoatomic_of_isAtomic_of_complementedLattice_of_isModular
-/
theorem isAtomic_iff_isCoatomic : IsAtomic α ↔ IsCoatomic α :=
  ⟨fun _ => isCoatomic_of_isAtomic_of_complementedLattice_of_isModular,
   fun _ => isAtomic_of_isCoatomic_of_complementedLattice_of_isModular⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ComplementedLattice.isStronglyAtomic` / 定理 `ComplementedLattice.isStronglyAtomic`

English:
theorem ComplementedLattice.isStronglyAtomic
  given: [IsAtomic α]
  statement: IsStronglyAtomic α where
  proof: by
    obtain ⟨⟨a', ha'b : a' <= b⟩, ha'⟩ := exists_isCompl (α := Set.Iic b) ⟨a, hab.le⟩
    obtain (rfl | ⟨d, hd⟩) := eq_bot_or_exists_atom_le a'
    · obtain rfl : a = b := by simpa [codisjoint_bot, ← Subtype.coe_inj] using ha'.codisjoint
exact False.elim hab.ne rfl
    refine ⟨d ⊔ a, IsUpperModularLattice.covBy_sup_of_inf_covBy ?_, sup_le (hd.2.trans ha'b) hab.le⟩
    convert! hd.1.bot_covBy
    rw [← le_bot_iff]; rw [← show a ⊓ a' = ⊥ by simpa using Subtype.coe_inj.2 ha'.inf_eq_bot]; rw [inf_comm]
    exact inf_le_inf_left _ hd.2

中文:
定理 有补格.isStronglyAtomic
  条件: [是原子的 α]
  结论: 是StronglyAtomic α where
  证明: by
    obtain ⟨⟨a', ha'b : a' <= b⟩, ha'⟩ := exists_isCompl (α := Set.Iic b) ⟨a, hab.le⟩
    obtain (rfl | ⟨d, hd⟩) := eq_bot_or_exists_atom_le a'
    · obtain rfl : a = b := by simpa [codisjoint_bot, ← Subtype.coe_inj] using ha'.codisjoint
exact False.elim hab.ne rfl
    refine ⟨d ⊔ a, IsUpperModularLattice.covBy_sup_of_inf_covBy ?_, sup_le (hd.2.trans ha'b) hab.le⟩
    convert! hd.1.bot_covBy
    rw [← le_bot_iff]; rw [← show a ⊓ a' = ⊥ by simpa using Subtype.coe_inj.2 ha'.inf_eq_bot]; rw [inf_comm]
    exact inf_le_inf_left _ hd.2

Depends on / 依赖: False.elim, IsUpperModularLattice, IsUpperModularLattice.covBy_sup_of_inf_covBy, Set.Iic, Subtype, Subtype.coe_inj, bot_covBy, codisjoint, codisjoint_bot, coe_inj, convert, covBy_sup_of_inf_covBy, eq_bot_or_exists_atom_le, exists_isCompl, hab.le, hab.ne, inf_comm, inf_eq_bot, inf_le_inf_, le_bot_iff
-/
theorem ComplementedLattice.isStronglyAtomic [IsAtomic α] : IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨⟨a', ha'b : a' <= b⟩, ha'⟩ := exists_isCompl (α := Set.Iic b) ⟨a, hab.le⟩
    obtain (rfl | ⟨d, hd⟩) := eq_bot_or_exists_atom_le a'
    · obtain rfl : a = b := by simpa [codisjoint_bot, ← Subtype.coe_inj] using ha'.codisjoint
exact False.elim hab.ne rfl
    refine ⟨d ⊔ a, IsUpperModularLattice.covBy_sup_of_inf_covBy ?_, sup_le (hd.2.trans ha'b) hab.le⟩
    convert! hd.1.bot_covBy
    rw [← le_bot_iff]; rw [← show a ⊓ a' = ⊥ by simpa using Subtype.coe_inj.2 ha'.inf_eq_bot]; rw [inf_comm]
    exact inf_le_inf_left _ hd.2

/--
theorem `ComplementedLattice.isStronglyCoatomic` / 定理 `ComplementedLattice.isStronglyCoatomic`

English:
theorem ComplementedLattice.isStronglyCoatomic
  given: [IsCoatomic α]
  statement: IsStronglyCoatomic α
  proof: isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 ComplementedLattice.isStronglyAtomic

中文:
定理 有补格.isStronglyCoatomic
  条件: [是余原子的 α]
  结论: 是StronglyCoatomic α
  证明: isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 ComplementedLattice.isStronglyAtomic

Depends on / 依赖: ComplementedLattice, ComplementedLattice.isStronglyAtomic, isStronglyAtomic, isStronglyAtomic_dual_iff_is_stronglyCoatomic
-/
theorem ComplementedLattice.isStronglyCoatomic [IsCoatomic α] : IsStronglyCoatomic α :=
isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 ComplementedLattice.isStronglyAtomic

/--
theorem `ComplementedLattice.isStronglyAtomic'` / 定理 `ComplementedLattice.isStronglyAtomic'`

English:
theorem ComplementedLattice.isStronglyAtomic'
  given: [h : IsAtomic α]
  statement: IsStronglyCoatomic α
  proof: by
  rw [isAtomic_iff_isCoatomic] at h
  exact isStronglyCoatomic

中文:
定理 有补格.isStronglyAtomic'
  条件: [h : 是原子的 α]
  结论: 是StronglyCoatomic α
  证明: by
  rw [isAtomic_iff_isCoatomic] at h
  exact isStronglyCoatomic

Depends on / 依赖: isAtomic_iff_isCoatomic, isStronglyCoatomic
-/
theorem ComplementedLattice.isStronglyAtomic' [h : IsAtomic α] : IsStronglyCoatomic α := by
  rw [isAtomic_iff_isCoatomic] at h
  exact isStronglyCoatomic

/--
theorem `ComplementedLattice.isStronglyCoatomic'` / 定理 `ComplementedLattice.isStronglyCoatomic'`

English:
theorem ComplementedLattice.isStronglyCoatomic'
  given: [h : IsCoatomic α]
  statement: IsStronglyAtomic α
  proof: by
  rw [← isAtomic_iff_isCoatomic] at h
  exact isStronglyAtomic

中文:
定理 有补格.isStronglyCoatomic'
  条件: [h : 是余原子的 α]
  结论: 是StronglyAtomic α
  证明: by
  rw [← isAtomic_iff_isCoatomic] at h
  exact isStronglyAtomic

Depends on / 依赖: isAtomic_iff_isCoatomic, isStronglyAtomic
-/
theorem ComplementedLattice.isStronglyCoatomic' [h : IsCoatomic α] : IsStronglyAtomic α := by
  rw [← isAtomic_iff_isCoatomic] at h
  exact isStronglyAtomic

end IsModularLattice

namespace «Prop»

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSimpleOrder Prop
  body: by simp [em']

中文:
实例 :
  签名: 是单序 命题
  定义体: by simp [em']
-/
instance : IsSimpleOrder Prop where
  eq_bot_or_eq_top p := by simp [em']

/--
theorem `isAtom_iff` / 定理 `isAtom_iff`

English:
theorem isAtom_iff
  given: {p : Prop}
  statement: IsAtom p ↔ p
  proof: by simp

中文:
定理 isAtom_iff
  条件: {p : 命题}
  结论: IsAtom p ↔ p
  证明: by simp
-/
theorem isAtom_iff {p : Prop} : IsAtom p ↔ p := by simp

/--
theorem `isCoatom_iff` / 定理 `isCoatom_iff`

English:
theorem isCoatom_iff
  given: {p : Prop}
  statement: IsCoatom p ↔ ¬ p
  proof: by simp

中文:
定理 isCoatom_iff
  条件: {p : 命题}
  结论: IsCoatom p ↔ ¬ p
  证明: by simp
-/
theorem isCoatom_iff {p : Prop} : IsCoatom p ↔ ¬ p := by simp

end «Prop»

namespace Pi

universe u
variable {ι : Type*} {π : ι -> Type u}

/--
theorem `eq_bot_iff` / 定理 `eq_bot_iff`

English:
theorem eq_bot_iff
  given: [forall i, Bot (π i)] {f : forall i, π i}
  statement: f = ⊥ ↔ forall i, f i = ⊥
  proof: funext_iff

中文:
定理 eq_bot_iff
  条件: [对任意 i, 底元素 (π i)] {f : 对任意 i, π i}
  结论: f = ⊥ ↔ 对任意 i, f i = ⊥
  证明: funext_iff
-/
protected theorem eq_bot_iff [forall i, Bot (π i)] {f : forall i, π i} : f = ⊥ ↔ forall i, f i = ⊥ :=
  funext_iff

/--
theorem `isAtom_iff` / 定理 `isAtom_iff`

English:
theorem isAtom_iff
  given: {f : forall i, π i} [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)]
  proof: by
  simp only [← bot_covBy_iff, Pi.covBy_iff, bot_apply, eq_comm]

中文:
定理 isAtom_iff
  条件: {f : 对任意 i, π i} [对任意 i, 偏序 (π i)] [对任意 i, 有底序 (π i)]
  证明: by
  simp only [← bot_covBy_iff, Pi.covBy_iff, bot_apply, eq_comm]

Depends on / 依赖: Pi.covBy_iff, bot_apply, bot_covBy_iff, covBy_iff, eq_comm
-/
theorem isAtom_iff {f : forall i, π i} [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)] :
    IsAtom f ↔ exists i, IsAtom (f i) ∧ forall j, j != i -> f j = ⊥ := by
  simp only [← bot_covBy_iff, Pi.covBy_iff, bot_apply, eq_comm]

/--
theorem `isAtom_single` / 定理 `isAtom_single`

English:
theorem isAtom_single
  statement: {i : ι} [DecidableEq ι] [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)]
  proof: isAtom_iff.2 ⟨i, by simpa, fun _ hji => Function.update_of_ne hji ..⟩

中文:
定理 isAtom_single
  结论: {i : ι} [DecidableEq ι] [对任意 i, 偏序 (π i)] [对任意 i, 有底序 (π i)]
  证明: isAtom_iff.2 ⟨i, by simpa, fun _ hji => Function.update_of_ne hji ..⟩

Depends on / 依赖: Function, Function.update_of_ne, isAtom_iff, update_of_ne
-/
theorem isAtom_single {i : ι} [DecidableEq ι] [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)]
    {a : π i} (h : IsAtom a) : IsAtom (Function.update (⊥ : forall i, π i) i a) :=
  isAtom_iff.2 ⟨i, by simpa, fun _ hji => Function.update_of_ne hji ..⟩

/--
theorem `isAtom_iff_eq_single` / 定理 `isAtom_iff_eq_single`

English:
theorem isAtom_iff_eq_single
  statement: [DecidableEq ι] [forall i, PartialOrder (π i)]
  proof: by
  simp [← bot_covBy_iff, covBy_iff_exists_right_eq]

中文:
定理 isAtom_iff_eq_single
  结论: [DecidableEq ι] [对任意 i, 偏序 (π i)]
  证明: by
  simp [← bot_covBy_iff, covBy_iff_exists_right_eq]

Depends on / 依赖: bot_covBy_iff, covBy_iff_exists_right_eq
-/
theorem isAtom_iff_eq_single [DecidableEq ι] [forall i, PartialOrder (π i)]
    [forall i, OrderBot (π i)] {f : forall i, π i} :
    IsAtom f ↔ exists i a, IsAtom a ∧ f = Function.update ⊥ i a := by
  simp [← bot_covBy_iff, covBy_iff_exists_right_eq]

/--
Instance `isAtomic` / 实例 `isAtomic`

English:
instance isAtomic
  signature: [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)] [forall i, IsAtomic (π i)]
  body: or_iff_not_imp_left.2 fun h =>
    have ⟨i, hi⟩ : exists i, b i != ⊥ := not_forall.1 (h.imp Pi.eq_bot_iff.2)
    have ⟨a, ha, hab⟩ := (eq_bot_or_exists_atom_le (b i)).resolve_left hi
    by classical exact ⟨Function.update ⊥ i a, isAtom_single ha, update_le_iff.2 ⟨hab, by simp⟩⟩

中文:
实例 isAtomic
  签名: [对任意 i, 偏序 (π i)] [对任意 i, 有底序 (π i)] [对任意 i, 是原子的 (π i)]
  定义体: or_iff_not_imp_left.2 fun h =>
    have ⟨i, hi⟩ : exists i, b i != ⊥ := not_forall.1 (h.imp Pi.eq_bot_iff.2)
    have ⟨a, ha, hab⟩ := (eq_bot_or_exists_atom_le (b i)).resolve_left hi
    by classical exact ⟨Function.update ⊥ i a, isAtom_single ha, update_le_iff.2 ⟨hab, by simp⟩⟩

Depends on / 依赖: or_iff_not_imp_left
-/
instance isAtomic [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)] [forall i, IsAtomic (π i)] :
    IsAtomic (forall i, π i) where
  eq_bot_or_exists_atom_le b := or_iff_not_imp_left.2 fun h =>
    have ⟨i, hi⟩ : exists i, b i != ⊥ := not_forall.1 (h.imp Pi.eq_bot_iff.2)
    have ⟨a, ha, hab⟩ := (eq_bot_or_exists_atom_le (b i)).resolve_left hi
    by classical exact ⟨Function.update ⊥ i a, isAtom_single ha, update_le_iff.2 ⟨hab, by simp⟩⟩

/--
Instance `isCoatomic` / 实例 `isCoatomic`

English:
instance isCoatomic
  signature: [forall i, PartialOrder (π i)] [forall i, OrderTop (π i)] [forall i, IsCoatomic (π i)]
  body: isAtomic_dual_iff_isCoatomic.1
    show IsAtomic (forall i, (π i)ᵒᵈ) from inferInstance

中文:
实例 isCoatomic
  签名: [对任意 i, 偏序 (π i)] [对任意 i, 有顶序 (π i)] [对任意 i, 是余原子的 (π i)]
  定义体: isAtomic_dual_iff_isCoatomic.1
    show IsAtomic (forall i, (π i)ᵒᵈ) from inferInstance

Depends on / 依赖: IsAtomic, isAtomic_dual_iff_isCoatomic
-/
instance isCoatomic [forall i, PartialOrder (π i)] [forall i, OrderTop (π i)] [forall i, IsCoatomic (π i)] :
    IsCoatomic (forall i, π i) :=
isAtomic_dual_iff_isCoatomic.1
    show IsAtomic (forall i, (π i)ᵒᵈ) from inferInstance

/--
Instance `isAtomistic` / 实例 `isAtomistic`

English:
instance isAtomistic
  signature: [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)] [forall i, IsAtomistic (π i)]
  body: by
    classical
    refine ⟨{f | IsAtom f ∧ f <= s}, ?_, by simp +contextual⟩
    rw [isLUB_pi]
    intro i
    simp_rw [isAtom_iff_eq_single]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨⟨_, _, _, rfl⟩, hs⟩, rfl⟩
      exact hs i
    · refine fun j hj => (isLUB_atoms_le (s i)).2 fun x ⟨hx₁, hx₂⟩ => ?_
      exact hj ⟨Function.update ⊥ i x, ⟨⟨_, x, hx₁, rfl⟩, by simp [update_le_iff, hx₂]⟩, by simp⟩

中文:
实例 isAtomistic
  签名: [对任意 i, 偏序 (π i)] [对任意 i, 有底序 (π i)] [对任意 i, 是Atomistic (π i)]
  定义体: by
    classical
    refine ⟨{f | IsAtom f ∧ f <= s}, ?_, by simp +contextual⟩
    rw [isLUB_pi]
    intro i
    simp_rw [isAtom_iff_eq_single]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨⟨_, _, _, rfl⟩, hs⟩, rfl⟩
      exact hs i
    · refine fun j hj => (isLUB_atoms_le (s i)).2 fun x ⟨hx₁, hx₂⟩ => ?_
      exact hj ⟨Function.update ⊥ i x, ⟨⟨_, x, hx₁, rfl⟩, by simp [update_le_iff, hx₂]⟩, by simp⟩

Depends on / 依赖: Function, Function.update, IsAtom, classical, contextual, isAtom_iff_eq_single, isLUB_atoms_le, isLUB_pi, simp_rw, update, update_le_iff
-/
instance isAtomistic [forall i, PartialOrder (π i)] [forall i, OrderBot (π i)] [forall i, IsAtomistic (π i)] :
    IsAtomistic (forall i, π i) where
  isLUB_atoms s := by
    classical
    refine ⟨{f | IsAtom f ∧ f <= s}, ?_, by simp +contextual⟩
    rw [isLUB_pi]
    intro i
    simp_rw [isAtom_iff_eq_single]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨⟨_, _, _, rfl⟩, hs⟩, rfl⟩
      exact hs i
    · refine fun j hj => (isLUB_atoms_le (s i)).2 fun x ⟨hx₁, hx₂⟩ => ?_
      exact hj ⟨Function.update ⊥ i x, ⟨⟨_, x, hx₁, rfl⟩, by simp [update_le_iff, hx₂]⟩, by simp⟩

/--
Instance `isCoatomistic` / 实例 `isCoatomistic`

English:
instance isCoatomistic
  signature: [forall i, CompleteLattice (π i)] [forall i, IsCoatomistic (π i)]
  body: isAtomistic_dual_iff_isCoatomistic.1
    show IsAtomistic (forall i, (π i)ᵒᵈ) from inferInstance

中文:
实例 isCoatomistic
  签名: [对任意 i, 完备格 (π i)] [对任意 i, 是余atomistic (π i)]
  定义体: isAtomistic_dual_iff_isCoatomistic.1
    show IsAtomistic (forall i, (π i)ᵒᵈ) from inferInstance

Depends on / 依赖: IsAtomistic, isAtomistic_dual_iff_isCoatomistic
-/
instance isCoatomistic [forall i, CompleteLattice (π i)] [forall i, IsCoatomistic (π i)] :
    IsCoatomistic (forall i, π i) :=
isAtomistic_dual_iff_isCoatomistic.1
    show IsAtomistic (forall i, (π i)ᵒᵈ) from inferInstance

end Pi

section BooleanAlgebra
variable [BooleanAlgebra α] {a b : α}

/--
lemma `isAtom_compl` / 引理 `isAtom_compl`

English:
lemma isAtom_compl
  statement: IsAtom aᶜ ↔ IsCoatom a
  proof: isCompl_compl.symm.isAtom_iff_isCoatom

中文:
引理 isAtom_compl
  结论: IsAtom aᶜ ↔ IsCoatom a
  证明: isCompl_compl.symm.isAtom_iff_isCoatom
-/
@[simp] lemma isAtom_compl : IsAtom aᶜ ↔ IsCoatom a := isCompl_compl.symm.isAtom_iff_isCoatom
/--
lemma `isCoatom_compl` / 引理 `isCoatom_compl`

English:
lemma isCoatom_compl
  statement: IsCoatom aᶜ ↔ IsAtom a
  proof: isCompl_compl.symm.isCoatom_iff_isAtom

protected alias ⟨IsAtom.of_compl, IsCoatom.compl⟩ := isAtom_compl
protected alias ⟨IsCoatom.of_compl, IsAtom.compl⟩ := isCoatom_compl

中文:
引理 isCoatom_compl
  结论: IsCoatom aᶜ ↔ IsAtom a
  证明: isCompl_compl.symm.isCoatom_iff_isAtom

protected alias ⟨IsAtom.of_compl, IsCoatom.compl⟩ := isAtom_compl
protected alias ⟨IsCoatom.of_compl, IsAtom.compl⟩ := isCoatom_compl
-/
@[simp] lemma isCoatom_compl : IsCoatom aᶜ ↔ IsAtom a := isCompl_compl.symm.isCoatom_iff_isAtom

protected alias ⟨IsAtom.of_compl, IsCoatom.compl⟩ := isAtom_compl
protected alias ⟨IsCoatom.of_compl, IsAtom.compl⟩ := isCoatom_compl

end BooleanAlgebra

namespace Set

/--
theorem `isAtom_singleton` / 定理 `isAtom_singleton`

English:
theorem isAtom_singleton
  given: (x : α)
  statement: IsAtom ({x} : Set α)
  proof: ⟨singleton_ne_empty _, fun _ hs => ssubset_singleton_iff.mp hs⟩

中文:
定理 isAtom_singleton
  条件: (x : α)
  结论: IsAtom ({x} : 集合 α)
  证明: ⟨singleton_ne_empty _, fun _ hs => ssubset_singleton_iff.mp hs⟩

Depends on / 依赖: singleton_ne_empty, ssubset_singleton_iff, ssubset_singleton_iff.mp
-/
theorem isAtom_singleton (x : α) : IsAtom ({x} : Set α) :=
  ⟨singleton_ne_empty _, fun _ hs => ssubset_singleton_iff.mp hs⟩

/--
theorem `isAtom_iff` / 定理 `isAtom_iff`

English:
theorem isAtom_iff
  given: {s : Set α}
  statement: IsAtom s ↔ exists x, s = {x}
  proof: by
  refine
    ⟨?_, by
      rintro ⟨x, rfl⟩
      exact isAtom_singleton x⟩
  rw [isAtom_iff_le_of_ge]; rw [bot_eq_empty]; rw [← nonempty_iff_ne_empty]
  rintro ⟨⟨x, hx⟩, hs⟩
  exact
    ⟨x, eq_singleton_iff_unique_mem.2
        ⟨hx, fun y hy => (hs {y} (singleton_ne_empty _) (singleton_subset_iff.2 hy) hx).symm⟩⟩

中文:
定理 isAtom_iff
  条件: {s : 集合 α}
  结论: IsAtom s ↔ 存在 x, s = {x}
  证明: by
  refine
    ⟨?_, by
      rintro ⟨x, rfl⟩
      exact isAtom_singleton x⟩
  rw [isAtom_iff_le_of_ge]; rw [bot_eq_empty]; rw [← nonempty_iff_ne_empty]
  rintro ⟨⟨x, hx⟩, hs⟩
  exact
    ⟨x, eq_singleton_iff_unique_mem.2
        ⟨hx, fun y hy => (hs {y} (singleton_ne_empty _) (singleton_subset_iff.2 hy) hx).symm⟩⟩

Depends on / 依赖: bot_eq_empty, eq_singleton_iff_unique_mem, isAtom_iff_le_of_ge, isAtom_singleton, nonempty_iff_ne_empty, singleton_ne_empty, singleton_subset_iff
-/
theorem isAtom_iff {s : Set α} : IsAtom s ↔ exists x, s = {x} := by
  refine
    ⟨?_, by
      rintro ⟨x, rfl⟩
      exact isAtom_singleton x⟩
  rw [isAtom_iff_le_of_ge]; rw [bot_eq_empty]; rw [← nonempty_iff_ne_empty]
  rintro ⟨⟨x, hx⟩, hs⟩
  exact
    ⟨x, eq_singleton_iff_unique_mem.2
        ⟨hx, fun y hy => (hs {y} (singleton_ne_empty _) (singleton_subset_iff.2 hy) hx).symm⟩⟩

/--
theorem `isCoatom_iff` / 定理 `isCoatom_iff`

English:
theorem isCoatom_iff
  given: (s : Set α)
  statement: IsCoatom s ↔ exists x, s = {x}ᶜ
  proof: by
  rw [isCompl_compl.isCoatom_iff_isAtom]; rw [isAtom_iff]
  simp_rw [@eq_comm _ s, compl_eq_comm]

中文:
定理 isCoatom_iff
  条件: (s : 集合 α)
  结论: IsCoatom s ↔ 存在 x, s = {x}ᶜ
  证明: by
  rw [isCompl_compl.isCoatom_iff_isAtom]; rw [isAtom_iff]
  simp_rw [@eq_comm _ s, compl_eq_comm]

Depends on / 依赖: compl_eq_comm, eq_comm, isAtom_iff, isCoatom_iff_isAtom, isCompl_compl, isCompl_compl.isCoatom_iff_isAtom, simp_rw
-/
theorem isCoatom_iff (s : Set α) : IsCoatom s ↔ exists x, s = {x}ᶜ := by
  rw [isCompl_compl.isCoatom_iff_isAtom]; rw [isAtom_iff]
  simp_rw [@eq_comm _ s, compl_eq_comm]

/--
theorem `isCoatom_singleton_compl` / 定理 `isCoatom_singleton_compl`

English:
theorem isCoatom_singleton_compl
  given: (x : α)
  statement: IsCoatom ({x}ᶜ : Set α)
  proof: (isCoatom_iff {x}ᶜ).mpr ⟨x, rfl⟩

中文:
定理 isCoatom_singleton_compl
  条件: (x : α)
  结论: IsCoatom ({x}ᶜ : 集合 α)
  证明: (isCoatom_iff {x}ᶜ).mpr ⟨x, rfl⟩

Depends on / 依赖: isCoatom_iff
-/
theorem isCoatom_singleton_compl (x : α) : IsCoatom ({x}ᶜ : Set α) :=
  (isCoatom_iff {x}ᶜ).mpr ⟨x, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAtomistic (Set α)
  body: inferInstance

中文:
实例 :
  签名: 是Atomistic (集合 α)
  定义体: inferInstance
-/
instance : IsAtomistic (Set α) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCoatomistic (Set α)
  body: inferInstance

中文:
实例 :
  签名: 是余atomistic (集合 α)
  定义体: inferInstance
-/
instance : IsCoatomistic (Set α) := inferInstance

end Set
