/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.SetNotation

/-!
# Definition of complete lattices

This file contains the definition of complete lattices with suprema/infima of arbitrary sets.

## Main definitions

* `sSup` and `sInf` are the supremum and the infimum of a set;
* `iSup (f : ι → α)` and `iInf (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `sSup` and `sInf` of the range of this function;
* class `CompleteLattice`: a bounded lattice such that `sSup s` is always the least upper boundary
  of `s` and `sInf s` is always the greatest lower boundary of `s`;
* class `CompleteLinearOrder`: a linear ordered complete lattice.

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

@[expose] public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι -> Sort*} {κ' : ι' -> Sort*}

@[to_dual]
/--
Instance `OrderDual.supSet` / 实例 `OrderDual.supSet`

English:
instance OrderDual.supSet
  signature: (α) [h : InfSet α]
  body: ⟨fun s => h.sInf s⟩

中文:
实例 OrderDual.supSet
  签名: (α) [h : 下确界集 α]
  定义体: ⟨fun s => h.sInf s⟩

Depends on / 依赖: h.sInf
-/
instance OrderDual.supSet (α) [h : InfSet α] : SupSet αᵒᵈ :=
  ⟨fun s => h.sInf s⟩

/--
Definition of `CompleteSemilatticeSup` / `CompleteSemilatticeSup` 的定义

English:
class CompleteSemilatticeSup
  parameters: (α : Type*)
  extends: PartialOrder α, SupSet α
  axioms and operations (1):
    - isLUB_sSup : forall s : Set α, IsLUB s (sSup s)

中文:
类 余mpleteSemilatticeSup
  参数: (α : 类型)
  继承: 偏序 α, 上确界集 α
  公理与运算 (1 个):
    - isLUB_sSup : 对任意 s : 集合 α, IsLUB s (sSup s)
-/
class CompleteSemilatticeSup (α : Type*) extends PartialOrder α, SupSet α where
  /-- Every set has a least upper bound. -/
  isLUB_sSup : forall s : Set α, IsLUB s (sSup s)

/-- Note that we rarely use `CompleteSemilatticeInf`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
@[to_dual]
/--
Definition of `CompleteSemilatticeInf` / `CompleteSemilatticeInf` 的定义

English:
class CompleteSemilatticeInf
  parameters: (α : Type*)
  extends: PartialOrder α, InfSet α
  axioms and operations (1):
    - isGLB_sInf : forall s : Set α, IsGLB s (sInf s)

中文:
类 余mpleteSemilatticeInf
  参数: (α : 类型)
  继承: 偏序 α, 下确界集 α
  公理与运算 (1 个):
    - isGLB_sInf : 对任意 s : 集合 α, IsGLB s (sInf s)
-/
class CompleteSemilatticeInf (α : Type*) extends PartialOrder α, InfSet α where
  /-- Every set has a greatest lower bound. -/
  isGLB_sInf : forall s : Set α, IsGLB s (sInf s)

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b l : α} {f : ι -> α}

@[to_dual]
/--
theorem `isLUB_sSup` / 定理 `isLUB_sSup`

English:
theorem isLUB_sSup
  given: (s : Set α)
  statement: IsLUB s (sSup s)
  proof: CompleteSemilatticeSup.isLUB_sSup _

@[to_dual sInf_le]

中文:
定理 isLUB_sSup
  条件: (s : 集合 α)
  结论: IsLUB s (sSup s)
  证明: CompleteSemilatticeSup.isLUB_sSup _

@[to_dual sInf_le]

Depends on / 依赖: CompleteSemilatticeSup, CompleteSemilatticeSup.isLUB_sSup, isLUB_sSup
-/
theorem isLUB_sSup (s : Set α) : IsLUB s (sSup s) :=
  CompleteSemilatticeSup.isLUB_sSup _

@[to_dual sInf_le]
/--
theorem `le_sSup` / 定理 `le_sSup`

English:
theorem le_sSup
  given: (h : a in s)
  statement: a <= sSup s
  proof: (isLUB_sSup s).1 h

@[to_dual le_sInf]

中文:
定理 le_sSup
  条件: (h : a in s)
  结论: a <= sSup s
  证明: (isLUB_sSup s).1 h

@[to_dual le_sInf]

Depends on / 依赖: isLUB_sSup
-/
theorem le_sSup (h : a in s) : a <= sSup s :=
  (isLUB_sSup s).1 h

@[to_dual le_sInf]
/--
theorem `sSup_le` / 定理 `sSup_le`

English:
theorem sSup_le
  given: (h : forall b in s, b <= a)
  statement: sSup s <= a
  proof: (isLUB_sSup s).2 h

@[to_dual]

中文:
定理 sSup_le
  条件: (h : 对任意 b in s, b <= a)
  结论: sSup s <= a
  证明: (isLUB_sSup s).2 h

@[to_dual]

Depends on / 依赖: isLUB_sSup
-/
theorem sSup_le (h : forall b in s, b <= a) : sSup s <= a :=
  (isLUB_sSup s).2 h

@[to_dual]
/--
lemma `isLUB_iff_sSup_eq` / 引理 `isLUB_iff_sSup_eq`

English:
lemma isLUB_iff_sSup_eq
  statement: IsLUB s a ↔ sSup s = a
  proof: ⟨(isLUB_sSup s).unique, by rintro rfl; exact isLUB_sSup _⟩

@[to_dual]
alias ⟨IsLUB.sSup_eq, _⟩ := isLUB_iff_sSup_eq

@[to_dual]

中文:
引理 isLUB_iff_sSup_eq
  结论: IsLUB s a ↔ sSup s = a
  证明: ⟨(isLUB_sSup s).unique, by rintro rfl; exact isLUB_sSup _⟩

@[to_dual]
alias ⟨IsLUB.sSup_eq, _⟩ := isLUB_iff_sSup_eq

@[to_dual]

Depends on / 依赖: isLUB_sSup, unique
-/
lemma isLUB_iff_sSup_eq : IsLUB s a ↔ sSup s = a :=
  ⟨(isLUB_sSup s).unique, by rintro rfl; exact isLUB_sSup _⟩

@[to_dual]
alias ⟨IsLUB.sSup_eq, _⟩ := isLUB_iff_sSup_eq

@[to_dual]
/--
theorem `sSup_mem_upperBounds` / 定理 `sSup_mem_upperBounds`

English:
theorem sSup_mem_upperBounds
  statement: sSup s in upperBounds s
  proof: (isLUB_le_iff <| isLUB_sSup s).mp refl _

@[to_dual sInf_le_of_le]

中文:
定理 sSup_mem_upperBounds
  结论: sSup s in upperBounds s
  证明: (isLUB_le_iff <| isLUB_sSup s).mp refl _

@[to_dual sInf_le_of_le]

Depends on / 依赖: isLUB_le_iff, isLUB_sSup
-/
theorem sSup_mem_upperBounds : sSup s in upperBounds s :=
(isLUB_le_iff <| isLUB_sSup s).mp refl _

@[to_dual sInf_le_of_le]
/--
theorem `le_sSup_of_le` / 定理 `le_sSup_of_le`

English:
theorem le_sSup_of_le
  given: (hb : b in s) (h : a <= b)
  statement: a <= sSup s
  proof: le_trans h (le_sSup hb)

@[to_dual (attr := gcongr)]

中文:
定理 le_sSup_of_le
  条件: (hb : b in s) (h : a <= b)
  结论: a <= sSup s
  证明: le_trans h (le_sSup hb)

@[to_dual (attr := gcongr)]

Depends on / 依赖: le_sSup, le_trans
-/
theorem le_sSup_of_le (hb : b in s) (h : a <= b) : a <= sSup s :=
  le_trans h (le_sSup hb)

@[to_dual (attr := gcongr)]
/--
theorem `sSup_le_sSup` / 定理 `sSup_le_sSup`

English:
theorem sSup_le_sSup
  given: (h : s subseteq t)
  statement: sSup s <= sSup t
  proof: (isLUB_sSup s).mono (isLUB_sSup t) h

@[to_dual (attr := simp) le_sInf_iff]

中文:
定理 sSup_le_sSup
  条件: (h : s subseteq t)
  结论: sSup s <= sSup t
  证明: (isLUB_sSup s).mono (isLUB_sSup t) h

@[to_dual (attr := simp) le_sInf_iff]

Depends on / 依赖: isLUB_sSup
-/
theorem sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t :=
  (isLUB_sSup s).mono (isLUB_sSup t) h

@[to_dual (attr := simp) le_sInf_iff]
/--
theorem `sSup_le_iff` / 定理 `sSup_le_iff`

English:
theorem sSup_le_iff
  statement: sSup s <= a ↔ forall b in s, b <= a
  proof: isLUB_le_iff (isLUB_sSup s)

@[to_dual sInf_le_iff]

中文:
定理 sSup_le_iff
  结论: sSup s <= a ↔ 对任意 b in s, b <= a
  证明: isLUB_le_iff (isLUB_sSup s)

@[to_dual sInf_le_iff]

Depends on / 依赖: isLUB_le_iff, isLUB_sSup
-/
theorem sSup_le_iff : sSup s <= a ↔ forall b in s, b <= a :=
  isLUB_le_iff (isLUB_sSup s)

@[to_dual sInf_le_iff]
/--
theorem `le_sSup_iff` / 定理 `le_sSup_iff`

English:
theorem le_sSup_iff
  statement: a <= sSup s ↔ forall b in upperBounds s, a <= b
  proof: ⟨fun h _ hb => le_trans h (sSup_le hb), fun hb => hb _ fun _ => le_sSup⟩

@[to_dual iInf_le_iff]

中文:
定理 le_sSup_iff
  结论: a <= sSup s ↔ 对任意 b in upperBounds s, a <= b
  证明: ⟨fun h _ hb => le_trans h (sSup_le hb), fun hb => hb _ fun _ => le_sSup⟩

@[to_dual iInf_le_iff]

Depends on / 依赖: le_sSup, le_trans, sSup_le
-/
theorem le_sSup_iff : a <= sSup s ↔ forall b in upperBounds s, a <= b :=
  ⟨fun h _ hb => le_trans h (sSup_le hb), fun hb => hb _ fun _ => le_sSup⟩

@[to_dual iInf_le_iff]
/--
theorem `le_iSup_iff` / 定理 `le_iSup_iff`

English:
theorem le_iSup_iff
  given: {s : ι -> α}
  statement: a <= iSup s ↔ forall b, (forall i, s i <= b) -> a <= b
  proof: by
  simp [iSup, le_sSup_iff, upperBounds]

@[to_dual lt_sInf_iff]

中文:
定理 le_iSup_iff
  条件: {s : ι -> α}
  结论: a <= iSup s ↔ 对任意 b, (对任意 i, s i <= b) -> a <= b
  证明: by
  simp [iSup, le_sSup_iff, upperBounds]

@[to_dual lt_sInf_iff]

Depends on / 依赖: le_sSup_iff, upperBounds
-/
theorem le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall i, s i <= b) -> a <= b := by
  simp [iSup, le_sSup_iff, upperBounds]

@[to_dual lt_sInf_iff]
/--
theorem `sSup_lt_iff` / 定理 `sSup_lt_iff`

English:
theorem sSup_lt_iff
  statement: sSup s < l ↔ exists b < l, b in upperBounds s where
  proof: ⟨sSup s, hsl, sSup_mem_upperBounds⟩
.trans_lt hbl mpr := fun ⟨_, hbl, hbs⟩ => sSup_le_iff.mpr hbs

@[to_dual lt_iInf_iff]

中文:
定理 sSup_lt_iff
  结论: sSup s < l ↔ 存在 b < l, b in upperBounds s where
  证明: ⟨sSup s, hsl, sSup_mem_upperBounds⟩
.trans_lt hbl mpr := fun ⟨_, hbl, hbs⟩ => sSup_le_iff.mpr hbs

@[to_dual lt_iInf_iff]

Depends on / 依赖: sSup_mem_upperBounds
-/
theorem sSup_lt_iff : sSup s < l ↔ exists b < l, b in upperBounds s where
  mp hsl := ⟨sSup s, hsl, sSup_mem_upperBounds⟩
.trans_lt hbl mpr := fun ⟨_, hbl, hbs⟩ => sSup_le_iff.mpr hbs

@[to_dual lt_iInf_iff]
/--
theorem `iSup_lt_iff` / 定理 `iSup_lt_iff`

English:
theorem iSup_lt_iff
  statement: iSup f < l ↔ exists b < l, forall i, f i <= b
  proof: sSup_lt_iff.trans exists_congr fun _ => and_congr_right fun _ => forall_mem_range

中文:
定理 iSup_lt_iff
  结论: iSup f < l ↔ 存在 b < l, 对任意 i, f i <= b
  证明: sSup_lt_iff.trans exists_congr fun _ => and_congr_right fun _ => forall_mem_range

Depends on / 依赖: and_congr_right, exists_congr, forall_mem_range, sSup_lt_iff, sSup_lt_iff.trans
-/
theorem iSup_lt_iff : iSup f < l ↔ exists b < l, forall i, f i <= b :=
sSup_lt_iff.trans exists_congr fun _ => and_congr_right fun _ => forall_mem_range

end

@[to_dual]
instance {α : Type*} [CompleteSemilatticeInf α] : CompleteSemilatticeSup αᵒᵈ where
  isLUB_sSup := isGLB_sInf (α := α)

/--
Definition of `CompleteLattice` / `CompleteLattice` 的定义

English:
class CompleteLattice
  parameters: (α : Type*)
  extends: Lattice α, CompleteSemilatticeSup α, 
  (no additional axioms)

中文:
类 完备格
  参数: (α : 类型)
  继承: 格 α, 余mpleteSemilatticeSup α, 
  (无附加公理)

Depends on / 依赖: CompleteLattice, CompleteLattice.mk, isGLB_sInf, isLUB_sSup, toInfSet, toSupSet
-/
class CompleteLattice (α : Type*) extends Lattice α, CompleteSemilatticeSup α,
    CompleteSemilatticeInf α, BoundedOrder α

attribute [to_dual existing] CompleteLattice.toCompleteSemilatticeInf CompleteLattice.toInfSet
attribute [to_dual self (reorder := toSupSet toInfSet, isLUB_sSup isGLB_sInf)] CompleteLattice.mk

-- Shortcut instance to ensure that the path
-- `CompleteLattice α → CompletePartialOrder α → PartialOrder α` isn't taken,
-- as it tricks `#min_imports` into believing `Order.CompletePartialOrder` is a necessary import.
-- See note [lower instance priority]
instance (priority := 100) CompleteLattice.toPartialOrder' [CompleteLattice α] : PartialOrder α :=
  inferInstance

/-- Create a `CompleteLattice` from a `PartialOrder` and `InfSet`
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities. If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sSup, bot, top
  __ := completeLatticeOfInf my_T _
```
-/
@[instance_reducible]
/--
Definition of `completeLatticeOfInf` / `completeLatticeOfInf` 的定义

English:
definition completeLatticeOfInf
  signature: (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
  body: H1; __ := H2
  bot := sInf univ
  bot_le _ := (isGLB_sInf univ).1 trivial
  top := sInf ∅
le_top a := (isGLB_sInf ∅).2 by simp
  sup a b := sInf { x : α | a <= x ∧ b <= x }
  inf a b := sInf {a, b}
  le_inf a b c hab hac := by
    apply (isGLB_sInf _).2
    simp [*]
inf_le_right _ _ := (isGLB_sInf _

中文:
定义 completeLatticeOfInf
  签名: (α : 类型) [H1 : 偏序 α] [H2 : 下确界集 α]
  定义体: H1; __ := H2
  bot := sInf univ
  bot_le _ := (isGLB_sInf univ).1 trivial
  top := sInf ∅
le_top a := (isGLB_sInf ∅).2 by simp
  sup a b := sInf { x : α | a <= x ∧ b <= x }
  inf a b := sInf {a, b}
  le_inf a b c hab hac := by
    apply (isGLB_sInf _).2
    simp [*]
inf_le_right _ _ := (isGLB_sInf _
-/
def completeLatticeOfInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
    (isGLB_sInf : forall s : Set α, IsGLB s (sInf s)) : CompleteLattice α where
  __ := H1; __ := H2
  bot := sInf univ
  bot_le _ := (isGLB_sInf univ).1 trivial
  top := sInf ∅
le_top a := (isGLB_sInf ∅).2 by simp
  sup a b := sInf { x : α | a <= x ∧ b <= x }
  inf a b := sInf {a, b}
  le_inf a b c hab hac := by
    apply (isGLB_sInf _).2
    simp [*]
inf_le_right _ _ := (isGLB_sInf _).1 mem_insert_of_mem _ mem_singleton _
inf_le_left _ _ := (isGLB_sInf _).1 mem_insert _ _
sup_le a b c hac hbc := (isGLB_sInf _).1 by simp [*]
  le_sup_left _ _ := (isGLB_sInf _).2 fun _ => And.left
  le_sup_right _ _ := (isGLB_sInf _).2 fun _ => And.right
  sSup s := sInf (upperBounds s)
  isGLB_sInf := isGLB_sInf
  isLUB_sSup s := isGLB_upperBounds.mp (isGLB_sInf _)

/-- Any `CompleteSemilatticeInf` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfInf`.
-/
@[instance_reducible]
/--
Definition of `completeLatticeOfCompleteSemilatticeInf` / `completeLatticeOfCompleteSemilatticeInf` 的定义

English:
definition completeLatticeOfCompleteSemilatticeInf
  signature: (α : Type*) [CompleteSemilatticeInf α]
  body: completeLatticeOfInf α fun s => isGLB_sInf s

中文:
定义 completeLatticeOfCompleteSemilatticeInf
  签名: (α : 类型) [余mpleteSemilatticeInf α]
  定义体: completeLatticeOfInf α fun s => isGLB_sInf s

Depends on / 依赖: completeLatticeOfInf, isGLB_sInf
-/
def completeLatticeOfCompleteSemilatticeInf (α : Type*) [CompleteSemilatticeInf α] :
    CompleteLattice α :=
  completeLatticeOfInf α fun s => isGLB_sInf s

/-- Create a `CompleteLattice` from a `PartialOrder` and `SupSet`
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities. If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sInf, bot, top
  __ := completeLatticeOfSup my_T _
```
-/
@[instance_reducible]
/--
Definition of `completeLatticeOfSup` / `completeLatticeOfSup` 的定义

English:
definition completeLatticeOfSup
  signature: (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
  body: H1; __ := H2
  top := sSup univ
  le_top _ := (isLUB_sSup univ).1 trivial
  bot := sSup ∅
bot_le x := (isLUB_sSup ∅).2 by simp
  sup a b := sSup {a, b}
  sup_le a b c hac hbc := (isLUB_sSup _).2 (by simp [*])
le_sup_left _ _ := (isLUB_sSup _).1 mem_insert _ _
le_sup_right _ _ := (isLUB_sSup _).1 mem

中文:
定义 completeLatticeOfSup
  签名: (α : 类型) [H1 : 偏序 α] [H2 : 上确界集 α]
  定义体: H1; __ := H2
  top := sSup univ
  le_top _ := (isLUB_sSup univ).1 trivial
  bot := sSup ∅
bot_le x := (isLUB_sSup ∅).2 by simp
  sup a b := sSup {a, b}
  sup_le a b c hac hbc := (isLUB_sSup _).2 (by simp [*])
le_sup_left _ _ := (isLUB_sSup _).1 mem_insert _ _
le_sup_right _ _ := (isLUB_sSup _).1 mem
-/
def completeLatticeOfSup (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (isLUB_sSup : forall s : Set α, IsLUB s (sSup s)) : CompleteLattice α where
  __ := H1; __ := H2
  top := sSup univ
  le_top _ := (isLUB_sSup univ).1 trivial
  bot := sSup ∅
bot_le x := (isLUB_sSup ∅).2 by simp
  sup a b := sSup {a, b}
  sup_le a b c hac hbc := (isLUB_sSup _).2 (by simp [*])
le_sup_left _ _ := (isLUB_sSup _).1 mem_insert _ _
le_sup_right _ _ := (isLUB_sSup _).1 mem_insert_of_mem _ mem_singleton _
  inf a b := sSup { x | x <= a ∧ x <= b }
le_inf a b c hab hac := (isLUB_sSup _).1 by simp [*]
  inf_le_left _ _ := (isLUB_sSup _).2 fun _ => And.left
  inf_le_right _ _ := (isLUB_sSup _).2 fun _ => And.right
  sInf s := sSup (lowerBounds s)
  isLUB_sSup := isLUB_sSup
  isGLB_sInf s := isLUB_lowerBounds.mp (isLUB_sSup _)

/-- Any `CompleteSemilatticeSup` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfSup`.
-/
@[instance_reducible]
/--
Definition of `completeLatticeOfCompleteSemilatticeSup` / `completeLatticeOfCompleteSemilatticeSup` 的定义

English:
definition completeLatticeOfCompleteSemilatticeSup
  signature: (α : Type*) [CompleteSemilatticeSup α]
  body: completeLatticeOfSup α fun s => isLUB_sSup s

中文:
定义 completeLatticeOfCompleteSemilatticeSup
  签名: (α : 类型) [余mpleteSemilatticeSup α]
  定义体: completeLatticeOfSup α fun s => isLUB_sSup s

Depends on / 依赖: completeLatticeOfSup, isLUB_sSup
-/
def completeLatticeOfCompleteSemilatticeSup (α : Type*) [CompleteSemilatticeSup α] :
    CompleteLattice α :=
  completeLatticeOfSup α fun s => isLUB_sSup s

-- Note that we do not use `extends LinearOrder α`,
-- and instead construct the forgetful instance manually.
/--
Definition of `CompleteLinearOrder` / `CompleteLinearOrder` 的定义

English:
class CompleteLinearOrder
  parameters: (α : Type*)
  extends: CompleteLattice α, BiheytingAlgebra α, Ord α
  axioms and operations (6):
    - le_total((a b : α)) : a <= b ∨ b <= a
    - toDecidableLE : DecidableLE α
    - toDecidableEq : DecidableEq α  [default: @decidableEqOfDecidableLE _ _ toDecidableLE]
    - toDecidableLT : DecidableLT α  [default: @decidableLTOfDecidableLE _ _ toDecidableLE]
    - compare(a b) : = compareOfLessAndEq a b
    - compare_eq_compareOfLessAndEq : forall a b, compare a b = compareOfLessAndEq a b  [default: by compareOfLessAndEq_rfl]

中文:
类 完备线性序
  参数: (α : 类型)
  继承: 完备格 α, Biheyting代数 α, 序 α
  公理与运算 (6 个):
    - le_total((a b : α)) : a <= b ∨ b <= a
    - toDecidableLE : DecidableLE α
    - toDecidableEq : DecidableEq α  [默认: @decidableEqOfDecidableLE _ _ toDecidableLE]
    - toDecidableLT : DecidableLT α  [默认: @decidableLTOfDecidableLE _ _ toDecidableLE]
    - compare(a b) : = compareOfLessAndEq a b
    - compare_eq_compareOfLessAndEq : 对任意 a b, compare a b = compareOfLessAndEq a b  [默认: by compareOfLessAndEq_rfl]

Depends on / 依赖: decidableEqOfDecidableLE, toDecidableLE
-/
class CompleteLinearOrder (α : Type*) extends CompleteLattice α, BiheytingAlgebra α, Ord α where
  /-- A linear order is total. -/
  le_total (a b : α) : a <= b ∨ b <= a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : forall a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

/--
Instance `CompleteLinearOrder.toLinearOrder` / 实例 `CompleteLinearOrder.toLinearOrder`

English:
instance CompleteLinearOrder.toLinearOrder
  signature: [i : CompleteLinearOrder α]
  body: i
  min_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]
  max_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]

中文:
实例 完备线性序.toLinearOrder
  签名: [i : 完备线性序 α]
  定义体: i
  min_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]
  max_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]
-/
instance CompleteLinearOrder.toLinearOrder [i : CompleteLinearOrder α] : LinearOrder α where
  __ := i
  min_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]
  max_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]

namespace OrderDual

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: [CompleteLattice α]

中文:
实例 instCompleteLattice
  签名: [完备格 α]
-/
instance instCompleteLattice [CompleteLattice α] : CompleteLattice αᵒᵈ where

/--
Instance `instCompleteLinearOrder` / 实例 `instCompleteLinearOrder`

English:
instance instCompleteLinearOrder
  signature: [CompleteLinearOrder α]
  body: instCompleteLattice
  __ := instBiheytingAlgebra
  __ := instLinearOrder α

中文:
实例 instCompleteLinearOrder
  签名: [完备线性序 α]
  定义体: instCompleteLattice
  __ := instBiheytingAlgebra
  __ := instLinearOrder α

Depends on / 依赖: instCompleteLattice
-/
instance instCompleteLinearOrder [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ where
  __ := instCompleteLattice
  __ := instBiheytingAlgebra
  __ := instLinearOrder α

end OrderDual

open OrderDual

section

section OrderDual

@[to_dual (attr := simp)]
/--
theorem `toDual_sSup` / 定理 `toDual_sSup`

English:
theorem toDual_sSup
  given: [SupSet α] (s : Set α)
  statement: toDual (sSup s) = sInf (ofDual ⁻¹' s)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDual_sSup
  条件: [上确界集 α] (s : 集合 α)
  结论: toDual (sSup s) = sInf (ofDual ⁻¹' s)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDual_sSup [SupSet α] (s : Set α) : toDual (sSup s) = sInf (ofDual ⁻¹' s) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `ofDual_sSup` / 定理 `ofDual_sSup`

English:
theorem ofDual_sSup
  given: [InfSet α] (s : Set αᵒᵈ)
  statement: ofDual (sSup s) = sInf (toDual ⁻¹' s)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 ofDual_sSup
  条件: [下确界集 α] (s : 集合 αᵒᵈ)
  结论: ofDual (sSup s) = sInf (toDual ⁻¹' s)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem ofDual_sSup [InfSet α] (s : Set αᵒᵈ) : ofDual (sSup s) = sInf (toDual ⁻¹' s) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `toDual_iSup` / 定理 `toDual_iSup`

English:
theorem toDual_iSup
  given: [SupSet α] (f : ι -> α)
  statement: toDual (⨆ i, f i) = ⨅ i, toDual (f i)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 toDual_iSup
  条件: [上确界集 α] (f : ι -> α)
  结论: toDual (⨆ i, f i) = ⨅ i, toDual (f i)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem toDual_iSup [SupSet α] (f : ι -> α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `ofDual_iSup` / 定理 `ofDual_iSup`

English:
theorem ofDual_iSup
  given: [InfSet α] (f : ι -> αᵒᵈ)
  statement: ofDual (⨆ i, f i) = ⨅ i, ofDual (f i)
  proof: rfl

中文:
定理 ofDual_iSup
  条件: [下确界集 α] (f : ι -> αᵒᵈ)
  结论: ofDual (⨆ i, f i) = ⨅ i, ofDual (f i)
  证明: rfl
-/
theorem ofDual_iSup [InfSet α] (f : ι -> αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f i) :=
  rfl

end OrderDual

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s : Set α} {a b l : α} {f : ι -> α}

@[to_dual sInf_lt_iff]
/--
theorem `lt_sSup_iff` / 定理 `lt_sSup_iff`

English:
theorem lt_sSup_iff
  statement: b < sSup s ↔ exists a in s, b < a
  proof: lt_isLUB_iff isLUB_sSup s

@[to_dual iInf_lt_iff]

中文:
定理 lt_sSup_iff
  结论: b < sSup s ↔ 存在 a in s, b < a
  证明: lt_isLUB_iff isLUB_sSup s

@[to_dual iInf_lt_iff]

Depends on / 依赖: TensorProduct, currently, defined, isLUB_sSup, lt_isLUB_iff, mathlib
-/
theorem lt_sSup_iff : b < sSup s ↔ exists a in s, b < a :=
lt_isLUB_iff isLUB_sSup s

@[to_dual iInf_lt_iff]
/--
theorem `lt_iSup_iff` / 定理 `lt_iSup_iff`

English:
theorem lt_iSup_iff
  statement: a < iSup f ↔ exists i, a < f i
  proof: lt_sSup_iff.trans exists_range_iff

@[to_dual sInf_le_iff_forall_lt]

中文:
定理 lt_iSup_iff
  结论: a < iSup f ↔ 存在 i, a < f i
  证明: lt_sSup_iff.trans exists_range_iff

@[to_dual sInf_le_iff_forall_lt]

Depends on / 依赖: exists_range_iff, lt_sSup_iff, lt_sSup_iff.trans
-/
theorem lt_iSup_iff : a < iSup f ↔ exists i, a < f i :=
  lt_sSup_iff.trans exists_range_iff

@[to_dual sInf_le_iff_forall_lt]
/--
theorem `le_sSup_iff_forall_lt` / 定理 `le_sSup_iff_forall_lt`

English:
theorem le_sSup_iff_forall_lt
  statement: l <= sSup s ↔ forall b < l, exists a in s, b < a
  proof: by
  grind [sSup_lt_iff, mem_upperBounds, not_le]

@[to_dual iInf_le_iff_forall_lt]

中文:
定理 le_sSup_iff_对任意_lt
  结论: l <= sSup s ↔ 对任意 b < l, 存在 a in s, b < a
  证明: by
  grind [sSup_lt_iff, mem_upperBounds, not_le]

@[to_dual iInf_le_iff_forall_lt]

Depends on / 依赖: mem_upperBounds, not_le, sSup_lt_iff
-/
theorem le_sSup_iff_forall_lt : l <= sSup s ↔ forall b < l, exists a in s, b < a := by
  grind [sSup_lt_iff, mem_upperBounds, not_le]

@[to_dual iInf_le_iff_forall_lt]
/--
theorem `le_iSup_iff_forall_lt` / 定理 `le_iSup_iff_forall_lt`

English:
theorem le_iSup_iff_forall_lt
  statement: l <= iSup f ↔ forall b < l, exists i, b < f i
  proof: le_sSup_iff_forall_lt.trans forall₂_congr fun _ _ => exists_range_iff

@[to_dual]

中文:
定理 le_iSup_iff_对任意_lt
  结论: l <= iSup f ↔ 对任意 b < l, 存在 i, b < f i
  证明: le_sSup_iff_forall_lt.trans forall₂_congr fun _ _ => exists_range_iff

@[to_dual]

Depends on / 依赖: exists_range_iff, le_sSup_iff_forall_lt, le_sSup_iff_forall_lt.trans
-/
theorem le_iSup_iff_forall_lt : l <= iSup f ↔ forall b < l, exists i, b < f i :=
le_sSup_iff_forall_lt.trans forall₂_congr fun _ _ => exists_range_iff

@[to_dual]
/--
theorem `sSup_eq_top` / 定理 `sSup_eq_top`

English:
theorem sSup_eq_top
  statement: sSup s = ⊤ ↔ forall b < ⊤, exists a in s, b < a
  proof: by
  rw [eq_top_iff]; rw [le_sSup_iff_forall_lt]

@[to_dual]

中文:
定理 sSup_eq_top
  结论: sSup s = ⊤ ↔ 对任意 b < ⊤, 存在 a in s, b < a
  证明: by
  rw [eq_top_iff]; rw [le_sSup_iff_forall_lt]

@[to_dual]

Depends on / 依赖: eq_top_iff, le_sSup_iff_forall_lt
-/
theorem sSup_eq_top : sSup s = ⊤ ↔ forall b < ⊤, exists a in s, b < a := by
  rw [eq_top_iff]; rw [le_sSup_iff_forall_lt]

@[to_dual]
/--
theorem `iSup_eq_top` / 定理 `iSup_eq_top`

English:
theorem iSup_eq_top
  statement: iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i
  proof: by
  rw [eq_top_iff]; rw [le_iSup_iff_forall_lt]

@[to_dual]

中文:
定理 iSup_eq_top
  结论: iSup f = ⊤ ↔ 对任意 b < ⊤, 存在 i, b < f i
  证明: by
  rw [eq_top_iff]; rw [le_iSup_iff_forall_lt]

@[to_dual]

Depends on / 依赖: eq_top_iff, le_iSup_iff_forall_lt
-/
theorem iSup_eq_top : iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i := by
  rw [eq_top_iff]; rw [le_iSup_iff_forall_lt]

@[to_dual]
/--
theorem `lt_biSup_iff` / 定理 `lt_biSup_iff`

English:
theorem lt_biSup_iff
  given: {s : Set β} {f : β -> α}
  statement: a < ⨆ i in s, f i ↔ exists i in s, a < f i
  proof: by
  simp [lt_iSup_iff]

中文:
定理 lt_biSup_iff
  条件: {s : 集合 β} {f : β -> α}
  结论: a < ⨆ i in s, f i ↔ 存在 i in s, a < f i
  证明: by
  simp [lt_iSup_iff]

Depends on / 依赖: lt_iSup_iff
-/
theorem lt_biSup_iff {s : Set β} {f : β -> α} : a < ⨆ i in s, f i ↔ exists i in s, a < f i := by
  simp [lt_iSup_iff]

end CompleteLinearOrder

end

namespace Equiv

variable (e : α ≃ β)

/--
Definition of `supSet` / `supSet` 的定义

English:
abbreviation supSet
  signature: [SupSet β]
  body: e.symm (⨆ a in s, e a)

中文:
缩写 supSet
  签名: [上确界集 β]
  定义体: e.symm (⨆ a in s, e a)
-/
protected abbrev supSet [SupSet β] : SupSet α where
  sSup s := e.symm (⨆ a in s, e a)

/--
lemma `supSet_def` / 引理 `supSet_def`

English:
lemma supSet_def
  given: [SupSet β] (s : Set α)
  proof: e.supSet
    sSup s = e.symm (⨆ a in s, e a) := rfl

中文:
引理 supSet_def
  条件: [上确界集 β] (s : 集合 α)
  证明: e.supSet
    sSup s = e.symm (⨆ a in s, e a) := rfl

Depends on / 依赖: e.supSet, supSet
-/
lemma supSet_def [SupSet β] (s : Set α) :
    letI := e.supSet
    sSup s = e.symm (⨆ a in s, e a) := rfl

/--
Definition of `infSet` / `infSet` 的定义

English:
abbreviation infSet
  signature: [InfSet β]
  body: e.symm (⨅ a in s, e a)

中文:
缩写 infSet
  签名: [下确界集 β]
  定义体: e.symm (⨅ a in s, e a)
-/
protected abbrev infSet [InfSet β] : InfSet α where
  sInf s := e.symm (⨅ a in s, e a)

/--
lemma `infSet_def` / 引理 `infSet_def`

English:
lemma infSet_def
  given: [InfSet β] (s : Set α)
  proof: e.infSet
    sInf s = e.symm (⨅ a in s, e a) := rfl

中文:
引理 infSet_def
  条件: [下确界集 β] (s : 集合 α)
  证明: e.infSet
    sInf s = e.symm (⨅ a in s, e a) := rfl

Depends on / 依赖: e.infSet, infSet
-/
lemma infSet_def [InfSet β] (s : Set α) :
    letI := e.infSet
    sInf s = e.symm (⨅ a in s, e a) := rfl

end Equiv
